module fibheapintvar 

open Integer6

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



fun FReach[] : set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22) {
  (QF.thiz_0).(QF.nodes_0).*(QF.fchild_0 + QF.fright_0) - null
}
one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16,N17,N18,N19,N20,N21,N22 extends FibHeapIntVarNode {}


one sig i320,i321,i322,i323,i324,i325,i326,i327,i328,i329,i3210,i3211,i3212,i3213,i3214,i3215,i3216,i3217,i3218,i3219,i3220,i3221,i3222,i3223 extends JavaPrimitiveIntegerValue {} 
fact {
	// int32 bounds 
	b01 in i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false+i3210->true+i3211->true+i3212->false+i3213->false+i3214->true+i3215->true+i3216->false+i3217->false+i3218->true+i3219->true+i3220->false+i3221->false+i3222->true+i3223->true
	i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false+i3210->true+i3211->true+i3212->false+i3213->false+i3214->true+i3215->true+i3216->false+i3217->false+i3218->true+i3219->true+i3220->false+i3221->false+i3222->true+i3223->true in b01
	b00 in i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true+i3210->false+i3211->true+i3212->false+i3213->true+i3214->false+i3215->true+i3216->false+i3217->true+i3218->false+i3219->true+i3220->false+i3221->true+i3222->false+i3223->true
	i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true+i3210->false+i3211->true+i3212->false+i3213->true+i3214->false+i3215->true+i3216->false+i3217->true+i3218->false+i3219->true+i3220->false+i3221->true+i3222->false+i3223->true in b00
	b05 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false+i3221->false+i3222->false+i3223->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false+i3221->false+i3222->false+i3223->false in b05
	b04 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->true+i3217->true+i3218->true+i3219->true+i3220->true+i3221->true+i3222->true+i3223->true
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->true+i3217->true+i3218->true+i3219->true+i3220->true+i3221->true+i3222->true+i3223->true in b04
	b03 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true+i3210->true+i3211->true+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false+i3221->false+i3222->false+i3223->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true+i3210->true+i3211->true+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false+i3221->false+i3222->false+i3223->false in b03
	b02 in i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false+i3210->false+i3211->false+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->true+i3221->true+i3222->true+i3223->true
	i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false+i3210->false+i3211->false+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->true+i3221->true+i3222->true+i3223->true in b02
}



fact { QF.fright_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->N14+N0->N15+N0->N16+N0->N17+N0->N18+N0->N19+N0->N20+N0->N21+N0->N22+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->N14+N1->N15+N1->N16+N1->N17+N1->N18+N1->N19+N1->N20+N1->N21+N1->N22+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->N14+N2->N15+N2->N16+N2->N17+N2->N18+N2->N19+N2->N20+N2->N21+N2->N22+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->N14+N3->N15+N3->N16+N3->N17+N3->N18+N3->N19+N3->N20+N3->N21+N3->N22+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->N14+N4->N15+N4->N16+N4->N17+N4->N18+N4->N19+N4->N20+N4->N21+N4->N22+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->N14+N5->N15+N5->N16+N5->N17+N5->N18+N5->N19+N5->N20+N5->N21+N5->N22+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->N14+N6->N15+N6->N16+N6->N17+N6->N18+N6->N19+N6->N20+N6->N21+N6->N22+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->N14+N7->N15+N7->N16+N7->N17+N7->N18+N7->N19+N7->N20+N7->N21+N7->N22+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->N14+N8->N15+N8->N16+N8->N17+N8->N18+N8->N19+N8->N20+N8->N21+N8->N22+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->N14+N9->N15+N9->N16+N9->N17+N9->N18+N9->N19+N9->N20+N9->N21+N9->N22+N9->null+N10->N11+N10->N12+N10->N13+N10->N14+N10->N15+N10->N16+N10->N17+N10->N18+N10->N19+N10->N20+N10->N21+N10->N22+N10->null+N11->N12+N11->N13+N11->N14+N11->N15+N11->N16+N11->N17+N11->N18+N11->N19+N11->N20+N11->N21+N11->N22+N11->null+N12->N13+N12->N14+N12->N15+N12->N16+N12->N17+N12->N18+N12->N19+N12->N20+N12->N21+N12->N22+N12->null+N13->N14+N13->N15+N13->N16+N13->N17+N13->N18+N13->N19+N13->N20+N13->N21+N13->N22+N13->null+N14->N15+N14->N16+N14->N17+N14->N18+N14->N19+N14->N20+N14->N21+N14->N22+N14->null+N15->N16+N15->N17+N15->N18+N15->N19+N15->N20+N15->N21+N15->N22+N15->null+N16->N17+N16->N18+N16->N19+N16->N20+N16->N21+N16->N22+N16->null+N17->N18+N17->N19+N17->N20+N17->N21+N17->N22+N17->null+N18->N19+N18->N20+N18->N21+N18->N22+N18->null+N19->N20+N19->N21+N19->N22+N19->null+N20->N21+N20->N22+N20->null+N21->N22+N21->null+N22->null }
fact { QF.fleft_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->N14+N0->N15+N0->N16+N0->N17+N0->N18+N0->N19+N0->N20+N0->N21+N0->N22+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->N14+N1->N15+N1->N16+N1->N17+N1->N18+N1->N19+N1->N20+N1->N21+N1->N22+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->N14+N2->N15+N2->N16+N2->N17+N2->N18+N2->N19+N2->N20+N2->N21+N2->N22+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->N14+N3->N15+N3->N16+N3->N17+N3->N18+N3->N19+N3->N20+N3->N21+N3->N22+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->N14+N4->N15+N4->N16+N4->N17+N4->N18+N4->N19+N4->N20+N4->N21+N4->N22+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->N14+N5->N15+N5->N16+N5->N17+N5->N18+N5->N19+N5->N20+N5->N21+N5->N22+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->N14+N6->N15+N6->N16+N6->N17+N6->N18+N6->N19+N6->N20+N6->N21+N6->N22+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->N14+N7->N15+N7->N16+N7->N17+N7->N18+N7->N19+N7->N20+N7->N21+N7->N22+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->N14+N8->N15+N8->N16+N8->N17+N8->N18+N8->N19+N8->N20+N8->N21+N8->N22+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->N14+N9->N15+N9->N16+N9->N17+N9->N18+N9->N19+N9->N20+N9->N21+N9->N22+N9->null+N10->N11+N10->N12+N10->N13+N10->N14+N10->N15+N10->N16+N10->N17+N10->N18+N10->N19+N10->N20+N10->N21+N10->N22+N10->null+N11->N12+N11->N13+N11->N14+N11->N15+N11->N16+N11->N17+N11->N18+N11->N19+N11->N20+N11->N21+N11->N22+N11->null+N12->N13+N12->N14+N12->N15+N12->N16+N12->N17+N12->N18+N12->N19+N12->N20+N12->N21+N12->N22+N12->null+N13->N14+N13->N15+N13->N16+N13->N17+N13->N18+N13->N19+N13->N20+N13->N21+N13->N22+N13->null+N14->N15+N14->N16+N14->N17+N14->N18+N14->N19+N14->N20+N14->N21+N14->N22+N14->null+N15->N16+N15->N17+N15->N18+N15->N19+N15->N20+N15->N21+N15->N22+N15->null+N16->N17+N16->N18+N16->N19+N16->N20+N16->N21+N16->N22+N16->null+N17->N18+N17->N19+N17->N20+N17->N21+N17->N22+N17->null+N18->N19+N18->N20+N18->N21+N18->N22+N18->null+N19->N20+N19->N21+N19->N22+N19->null+N20->N21+N20->N22+N20->null+N21->N22+N21->null+N22->null }
fact { QF.fchild_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->N14+N0->N15+N0->N16+N0->N17+N0->N18+N0->N19+N0->N20+N0->N21+N0->N22+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->N14+N1->N15+N1->N16+N1->N17+N1->N18+N1->N19+N1->N20+N1->N21+N1->N22+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->N14+N2->N15+N2->N16+N2->N17+N2->N18+N2->N19+N2->N20+N2->N21+N2->N22+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->N14+N3->N15+N3->N16+N3->N17+N3->N18+N3->N19+N3->N20+N3->N21+N3->N22+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->N14+N4->N15+N4->N16+N4->N17+N4->N18+N4->N19+N4->N20+N4->N21+N4->N22+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->N14+N5->N15+N5->N16+N5->N17+N5->N18+N5->N19+N5->N20+N5->N21+N5->N22+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->N14+N6->N15+N6->N16+N6->N17+N6->N18+N6->N19+N6->N20+N6->N21+N6->N22+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->N14+N7->N15+N7->N16+N7->N17+N7->N18+N7->N19+N7->N20+N7->N21+N7->N22+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->N14+N8->N15+N8->N16+N8->N17+N8->N18+N8->N19+N8->N20+N8->N21+N8->N22+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->N14+N9->N15+N9->N16+N9->N17+N9->N18+N9->N19+N9->N20+N9->N21+N9->N22+N9->null+N10->N11+N10->N12+N10->N13+N10->N14+N10->N15+N10->N16+N10->N17+N10->N18+N10->N19+N10->N20+N10->N21+N10->N22+N10->null+N11->N12+N11->N13+N11->N14+N11->N15+N11->N16+N11->N17+N11->N18+N11->N19+N11->N20+N11->N21+N11->N22+N11->null+N12->N13+N12->N14+N12->N15+N12->N16+N12->N17+N12->N18+N12->N19+N12->N20+N12->N21+N12->N22+N12->null+N13->N14+N13->N15+N13->N16+N13->N17+N13->N18+N13->N19+N13->N20+N13->N21+N13->N22+N13->null+N14->N15+N14->N16+N14->N17+N14->N18+N14->N19+N14->N20+N14->N21+N14->N22+N14->null+N15->N16+N15->N17+N15->N18+N15->N19+N15->N20+N15->N21+N15->N22+N15->null+N16->N17+N16->N18+N16->N19+N16->N20+N16->N21+N16->N22+N16->null+N17->N18+N17->N19+N17->N20+N17->N21+N17->N22+N17->null+N18->N19+N18->N20+N18->N21+N18->N22+N18->null+N19->N20+N19->N21+N19->N22+N19->null+N20->N21+N20->N22+N20->null+N21->N22+N21->null+N22->null }
fact { QF.fparent_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->N14+N0->N15+N0->N16+N0->N17+N0->N18+N0->N19+N0->N20+N0->N21+N0->N22+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->N14+N1->N15+N1->N16+N1->N17+N1->N18+N1->N19+N1->N20+N1->N21+N1->N22+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->N14+N2->N15+N2->N16+N2->N17+N2->N18+N2->N19+N2->N20+N2->N21+N2->N22+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->N14+N3->N15+N3->N16+N3->N17+N3->N18+N3->N19+N3->N20+N3->N21+N3->N22+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->N14+N4->N15+N4->N16+N4->N17+N4->N18+N4->N19+N4->N20+N4->N21+N4->N22+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->N14+N5->N15+N5->N16+N5->N17+N5->N18+N5->N19+N5->N20+N5->N21+N5->N22+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->N14+N6->N15+N6->N16+N6->N17+N6->N18+N6->N19+N6->N20+N6->N21+N6->N22+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->N14+N7->N15+N7->N16+N7->N17+N7->N18+N7->N19+N7->N20+N7->N21+N7->N22+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->N14+N8->N15+N8->N16+N8->N17+N8->N18+N8->N19+N8->N20+N8->N21+N8->N22+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->N14+N9->N15+N9->N16+N9->N17+N9->N18+N9->N19+N9->N20+N9->N21+N9->N22+N9->null+N10->N11+N10->N12+N10->N13+N10->N14+N10->N15+N10->N16+N10->N17+N10->N18+N10->N19+N10->N20+N10->N21+N10->N22+N10->null+N11->N12+N11->N13+N11->N14+N11->N15+N11->N16+N11->N17+N11->N18+N11->N19+N11->N20+N11->N21+N11->N22+N11->null+N12->N13+N12->N14+N12->N15+N12->N16+N12->N17+N12->N18+N12->N19+N12->N20+N12->N21+N12->N22+N12->null+N13->N14+N13->N15+N13->N16+N13->N17+N13->N18+N13->N19+N13->N20+N13->N21+N13->N22+N13->null+N14->N15+N14->N16+N14->N17+N14->N18+N14->N19+N14->N20+N14->N21+N14->N22+N14->null+N15->N16+N15->N17+N15->N18+N15->N19+N15->N20+N15->N21+N15->N22+N15->null+N16->N17+N16->N18+N16->N19+N16->N20+N16->N21+N16->N22+N16->null+N17->N18+N17->N19+N17->N20+N17->N21+N17->N22+N17->null+N18->N19+N18->N20+N18->N21+N18->N22+N18->null+N19->N20+N19->N21+N19->N22+N19->null+N20->N21+N20->N22+N20->null+N21->N22+N21->null+N22->null }
fact { QF.bright_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13+N14->N0+N14->N1+N14->N2+N14->N3+N14->N4+N14->N5+N14->N6+N14->N7+N14->N8+N14->N9+N14->N10+N14->N11+N14->N12+N14->N13+N14->N14+N15->N0+N15->N1+N15->N2+N15->N3+N15->N4+N15->N5+N15->N6+N15->N7+N15->N8+N15->N9+N15->N10+N15->N11+N15->N12+N15->N13+N15->N14+N15->N15+N16->N0+N16->N1+N16->N2+N16->N3+N16->N4+N16->N5+N16->N6+N16->N7+N16->N8+N16->N9+N16->N10+N16->N11+N16->N12+N16->N13+N16->N14+N16->N15+N16->N16+N17->N0+N17->N1+N17->N2+N17->N3+N17->N4+N17->N5+N17->N6+N17->N7+N17->N8+N17->N9+N17->N10+N17->N11+N17->N12+N17->N13+N17->N14+N17->N15+N17->N16+N17->N17+N18->N0+N18->N1+N18->N2+N18->N3+N18->N4+N18->N5+N18->N6+N18->N7+N18->N8+N18->N9+N18->N10+N18->N11+N18->N12+N18->N13+N18->N14+N18->N15+N18->N16+N18->N17+N18->N18+N19->N0+N19->N1+N19->N2+N19->N3+N19->N4+N19->N5+N19->N6+N19->N7+N19->N8+N19->N9+N19->N10+N19->N11+N19->N12+N19->N13+N19->N14+N19->N15+N19->N16+N19->N17+N19->N18+N19->N19+N20->N0+N20->N1+N20->N2+N20->N3+N20->N4+N20->N5+N20->N6+N20->N7+N20->N8+N20->N9+N20->N10+N20->N11+N20->N12+N20->N13+N20->N14+N20->N15+N20->N16+N20->N17+N20->N18+N20->N19+N20->N20+N21->N0+N21->N1+N21->N2+N21->N3+N21->N4+N21->N5+N21->N6+N21->N7+N21->N8+N21->N9+N21->N10+N21->N11+N21->N12+N21->N13+N21->N14+N21->N15+N21->N16+N21->N17+N21->N18+N21->N19+N21->N20+N21->N21+N22->N0+N22->N1+N22->N2+N22->N3+N22->N4+N22->N5+N22->N6+N22->N7+N22->N8+N22->N9+N22->N10+N22->N11+N22->N12+N22->N13+N22->N14+N22->N15+N22->N16+N22->N17+N22->N18+N22->N19+N22->N20+N22->N21+N22->N22 }
fact { QF.bleft_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13+N14->N0+N14->N1+N14->N2+N14->N3+N14->N4+N14->N5+N14->N6+N14->N7+N14->N8+N14->N9+N14->N10+N14->N11+N14->N12+N14->N13+N14->N14+N15->N0+N15->N1+N15->N2+N15->N3+N15->N4+N15->N5+N15->N6+N15->N7+N15->N8+N15->N9+N15->N10+N15->N11+N15->N12+N15->N13+N15->N14+N15->N15+N16->N0+N16->N1+N16->N2+N16->N3+N16->N4+N16->N5+N16->N6+N16->N7+N16->N8+N16->N9+N16->N10+N16->N11+N16->N12+N16->N13+N16->N14+N16->N15+N16->N16+N17->N0+N17->N1+N17->N2+N17->N3+N17->N4+N17->N5+N17->N6+N17->N7+N17->N8+N17->N9+N17->N10+N17->N11+N17->N12+N17->N13+N17->N14+N17->N15+N17->N16+N17->N17+N18->N0+N18->N1+N18->N2+N18->N3+N18->N4+N18->N5+N18->N6+N18->N7+N18->N8+N18->N9+N18->N10+N18->N11+N18->N12+N18->N13+N18->N14+N18->N15+N18->N16+N18->N17+N18->N18+N19->N0+N19->N1+N19->N2+N19->N3+N19->N4+N19->N5+N19->N6+N19->N7+N19->N8+N19->N9+N19->N10+N19->N11+N19->N12+N19->N13+N19->N14+N19->N15+N19->N16+N19->N17+N19->N18+N19->N19+N20->N0+N20->N1+N20->N2+N20->N3+N20->N4+N20->N5+N20->N6+N20->N7+N20->N8+N20->N9+N20->N10+N20->N11+N20->N12+N20->N13+N20->N14+N20->N15+N20->N16+N20->N17+N20->N18+N20->N19+N20->N20+N21->N0+N21->N1+N21->N2+N21->N3+N21->N4+N21->N5+N21->N6+N21->N7+N21->N8+N21->N9+N21->N10+N21->N11+N21->N12+N21->N13+N21->N14+N21->N15+N21->N16+N21->N17+N21->N18+N21->N19+N21->N20+N21->N21+N22->N0+N22->N1+N22->N2+N22->N3+N22->N4+N22->N5+N22->N6+N22->N7+N22->N8+N22->N9+N22->N10+N22->N11+N22->N12+N22->N13+N22->N14+N22->N15+N22->N16+N22->N17+N22->N18+N22->N19+N22->N20+N22->N21+N22->N22 }
fact { QF.bchild_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13+N14->N0+N14->N1+N14->N2+N14->N3+N14->N4+N14->N5+N14->N6+N14->N7+N14->N8+N14->N9+N14->N10+N14->N11+N14->N12+N14->N13+N14->N14+N15->N0+N15->N1+N15->N2+N15->N3+N15->N4+N15->N5+N15->N6+N15->N7+N15->N8+N15->N9+N15->N10+N15->N11+N15->N12+N15->N13+N15->N14+N15->N15+N16->N0+N16->N1+N16->N2+N16->N3+N16->N4+N16->N5+N16->N6+N16->N7+N16->N8+N16->N9+N16->N10+N16->N11+N16->N12+N16->N13+N16->N14+N16->N15+N16->N16+N17->N0+N17->N1+N17->N2+N17->N3+N17->N4+N17->N5+N17->N6+N17->N7+N17->N8+N17->N9+N17->N10+N17->N11+N17->N12+N17->N13+N17->N14+N17->N15+N17->N16+N17->N17+N18->N0+N18->N1+N18->N2+N18->N3+N18->N4+N18->N5+N18->N6+N18->N7+N18->N8+N18->N9+N18->N10+N18->N11+N18->N12+N18->N13+N18->N14+N18->N15+N18->N16+N18->N17+N18->N18+N19->N0+N19->N1+N19->N2+N19->N3+N19->N4+N19->N5+N19->N6+N19->N7+N19->N8+N19->N9+N19->N10+N19->N11+N19->N12+N19->N13+N19->N14+N19->N15+N19->N16+N19->N17+N19->N18+N19->N19+N20->N0+N20->N1+N20->N2+N20->N3+N20->N4+N20->N5+N20->N6+N20->N7+N20->N8+N20->N9+N20->N10+N20->N11+N20->N12+N20->N13+N20->N14+N20->N15+N20->N16+N20->N17+N20->N18+N20->N19+N20->N20+N21->N0+N21->N1+N21->N2+N21->N3+N21->N4+N21->N5+N21->N6+N21->N7+N21->N8+N21->N9+N21->N10+N21->N11+N21->N12+N21->N13+N21->N14+N21->N15+N21->N16+N21->N17+N21->N18+N21->N19+N21->N20+N21->N21+N22->N0+N22->N1+N22->N2+N22->N3+N22->N4+N22->N5+N22->N6+N22->N7+N22->N8+N22->N9+N22->N10+N22->N11+N22->N12+N22->N13+N22->N14+N22->N15+N22->N16+N22->N17+N22->N18+N22->N19+N22->N20+N22->N21+N22->N22 }
fact { QF.bparent_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13+N14->N0+N14->N1+N14->N2+N14->N3+N14->N4+N14->N5+N14->N6+N14->N7+N14->N8+N14->N9+N14->N10+N14->N11+N14->N12+N14->N13+N14->N14+N15->N0+N15->N1+N15->N2+N15->N3+N15->N4+N15->N5+N15->N6+N15->N7+N15->N8+N15->N9+N15->N10+N15->N11+N15->N12+N15->N13+N15->N14+N15->N15+N16->N0+N16->N1+N16->N2+N16->N3+N16->N4+N16->N5+N16->N6+N16->N7+N16->N8+N16->N9+N16->N10+N16->N11+N16->N12+N16->N13+N16->N14+N16->N15+N16->N16+N17->N0+N17->N1+N17->N2+N17->N3+N17->N4+N17->N5+N17->N6+N17->N7+N17->N8+N17->N9+N17->N10+N17->N11+N17->N12+N17->N13+N17->N14+N17->N15+N17->N16+N17->N17+N18->N0+N18->N1+N18->N2+N18->N3+N18->N4+N18->N5+N18->N6+N18->N7+N18->N8+N18->N9+N18->N10+N18->N11+N18->N12+N18->N13+N18->N14+N18->N15+N18->N16+N18->N17+N18->N18+N19->N0+N19->N1+N19->N2+N19->N3+N19->N4+N19->N5+N19->N6+N19->N7+N19->N8+N19->N9+N19->N10+N19->N11+N19->N12+N19->N13+N19->N14+N19->N15+N19->N16+N19->N17+N19->N18+N19->N19+N20->N0+N20->N1+N20->N2+N20->N3+N20->N4+N20->N5+N20->N6+N20->N7+N20->N8+N20->N9+N20->N10+N20->N11+N20->N12+N20->N13+N20->N14+N20->N15+N20->N16+N20->N17+N20->N18+N20->N19+N20->N20+N21->N0+N21->N1+N21->N2+N21->N3+N21->N4+N21->N5+N21->N6+N21->N7+N21->N8+N21->N9+N21->N10+N21->N11+N21->N12+N21->N13+N21->N14+N21->N15+N21->N16+N21->N17+N21->N18+N21->N19+N21->N20+N21->N21+N22->N0+N22->N1+N22->N2+N22->N3+N22->N4+N22->N5+N22->N6+N22->N7+N22->N8+N22->N9+N22->N10+N22->N11+N22->N12+N22->N13+N22->N14+N22->N15+N22->N16+N22->N17+N22->N18+N22->N19+N22->N20+N22->N21+N22->N22 }


fact {
	(QF.key_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->i329+N0->i3210+N0->i3211+N0->i3212+N0->i3213+N0->i3214+N0->i3215+N0->i3216+N0->i3217+N0->i3218+N0->i3219+N0->i3220+N0->i3221+N0->i3222+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->i329+N1->i3210+N1->i3211+N1->i3212+N1->i3213+N1->i3214+N1->i3215+N1->i3216+N1->i3217+N1->i3218+N1->i3219+N1->i3220+N1->i3221+N1->i3222+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->i329+N2->i3210+N2->i3211+N2->i3212+N2->i3213+N2->i3214+N2->i3215+N2->i3216+N2->i3217+N2->i3218+N2->i3219+N2->i3220+N2->i3221+N2->i3222+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->i329+N3->i3210+N3->i3211+N3->i3212+N3->i3213+N3->i3214+N3->i3215+N3->i3216+N3->i3217+N3->i3218+N3->i3219+N3->i3220+N3->i3221+N3->i3222+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->i329+N4->i3210+N4->i3211+N4->i3212+N4->i3213+N4->i3214+N4->i3215+N4->i3216+N4->i3217+N4->i3218+N4->i3219+N4->i3220+N4->i3221+N4->i3222+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->i329+N5->i3210+N5->i3211+N5->i3212+N5->i3213+N5->i3214+N5->i3215+N5->i3216+N5->i3217+N5->i3218+N5->i3219+N5->i3220+N5->i3221+N5->i3222+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->i329+N6->i3210+N6->i3211+N6->i3212+N6->i3213+N6->i3214+N6->i3215+N6->i3216+N6->i3217+N6->i3218+N6->i3219+N6->i3220+N6->i3221+N6->i3222+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->i329+N7->i3210+N7->i3211+N7->i3212+N7->i3213+N7->i3214+N7->i3215+N7->i3216+N7->i3217+N7->i3218+N7->i3219+N7->i3220+N7->i3221+N7->i3222+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->i329+N8->i3210+N8->i3211+N8->i3212+N8->i3213+N8->i3214+N8->i3215+N8->i3216+N8->i3217+N8->i3218+N8->i3219+N8->i3220+N8->i3221+N8->i3222+N8->null+N9->i320+N9->i321+N9->i322+N9->i323+N9->i324+N9->i325+N9->i326+N9->i327+N9->i328+N9->i329+N9->i3210+N9->i3211+N9->i3212+N9->i3213+N9->i3214+N9->i3215+N9->i3216+N9->i3217+N9->i3218+N9->i3219+N9->i3220+N9->i3221+N9->i3222+N9->null+N10->i320+N10->i321+N10->i322+N10->i323+N10->i324+N10->i325+N10->i326+N10->i327+N10->i328+N10->i329+N10->i3210+N10->i3211+N10->i3212+N10->i3213+N10->i3214+N10->i3215+N10->i3216+N10->i3217+N10->i3218+N10->i3219+N10->i3220+N10->i3221+N10->i3222+N10->null+N11->i320+N11->i321+N11->i322+N11->i323+N11->i324+N11->i325+N11->i326+N11->i327+N11->i328+N11->i329+N11->i3210+N11->i3211+N11->i3212+N11->i3213+N11->i3214+N11->i3215+N11->i3216+N11->i3217+N11->i3218+N11->i3219+N11->i3220+N11->i3221+N11->i3222+N11->null+N12->i320+N12->i321+N12->i322+N12->i323+N12->i324+N12->i325+N12->i326+N12->i327+N12->i328+N12->i329+N12->i3210+N12->i3211+N12->i3212+N12->i3213+N12->i3214+N12->i3215+N12->i3216+N12->i3217+N12->i3218+N12->i3219+N12->i3220+N12->i3221+N12->i3222+N12->null+N13->i320+N13->i321+N13->i322+N13->i323+N13->i324+N13->i325+N13->i326+N13->i327+N13->i328+N13->i329+N13->i3210+N13->i3211+N13->i3212+N13->i3213+N13->i3214+N13->i3215+N13->i3216+N13->i3217+N13->i3218+N13->i3219+N13->i3220+N13->i3221+N13->i3222+N13->null+N14->i320+N14->i321+N14->i322+N14->i323+N14->i324+N14->i325+N14->i326+N14->i327+N14->i328+N14->i329+N14->i3210+N14->i3211+N14->i3212+N14->i3213+N14->i3214+N14->i3215+N14->i3216+N14->i3217+N14->i3218+N14->i3219+N14->i3220+N14->i3221+N14->i3222+N14->null+N15->i320+N15->i321+N15->i322+N15->i323+N15->i324+N15->i325+N15->i326+N15->i327+N15->i328+N15->i329+N15->i3210+N15->i3211+N15->i3212+N15->i3213+N15->i3214+N15->i3215+N15->i3216+N15->i3217+N15->i3218+N15->i3219+N15->i3220+N15->i3221+N15->i3222+N15->null+N16->i320+N16->i321+N16->i322+N16->i323+N16->i324+N16->i325+N16->i326+N16->i327+N16->i328+N16->i329+N16->i3210+N16->i3211+N16->i3212+N16->i3213+N16->i3214+N16->i3215+N16->i3216+N16->i3217+N16->i3218+N16->i3219+N16->i3220+N16->i3221+N16->i3222+N16->null+N17->i320+N17->i321+N17->i322+N17->i323+N17->i324+N17->i325+N17->i326+N17->i327+N17->i328+N17->i329+N17->i3210+N17->i3211+N17->i3212+N17->i3213+N17->i3214+N17->i3215+N17->i3216+N17->i3217+N17->i3218+N17->i3219+N17->i3220+N17->i3221+N17->i3222+N17->null+N18->i320+N18->i321+N18->i322+N18->i323+N18->i324+N18->i325+N18->i326+N18->i327+N18->i328+N18->i329+N18->i3210+N18->i3211+N18->i3212+N18->i3213+N18->i3214+N18->i3215+N18->i3216+N18->i3217+N18->i3218+N18->i3219+N18->i3220+N18->i3221+N18->i3222+N18->null+N19->i320+N19->i321+N19->i322+N19->i323+N19->i324+N19->i325+N19->i326+N19->i327+N19->i328+N19->i329+N19->i3210+N19->i3211+N19->i3212+N19->i3213+N19->i3214+N19->i3215+N19->i3216+N19->i3217+N19->i3218+N19->i3219+N19->i3220+N19->i3221+N19->i3222+N19->null+N20->i320+N20->i321+N20->i322+N20->i323+N20->i324+N20->i325+N20->i326+N20->i327+N20->i328+N20->i329+N20->i3210+N20->i3211+N20->i3212+N20->i3213+N20->i3214+N20->i3215+N20->i3216+N20->i3217+N20->i3218+N20->i3219+N20->i3220+N20->i3221+N20->i3222+N20->null+N21->i320+N21->i321+N21->i322+N21->i323+N21->i324+N21->i325+N21->i326+N21->i327+N21->i328+N21->i329+N21->i3210+N21->i3211+N21->i3212+N21->i3213+N21->i3214+N21->i3215+N21->i3216+N21->i3217+N21->i3218+N21->i3219+N21->i3220+N21->i3221+N21->i3222+N21->null+N22->i320+N22->i321+N22->i322+N22->i323+N22->i324+N22->i325+N22->i326+N22->i327+N22->i328+N22->i329+N22->i3210+N22->i3211+N22->i3212+N22->i3213+N22->i3214+N22->i3215+N22->i3216+N22->i3217+N22->i3218+N22->i3219+N22->i3220+N22->i3221+N22->i3222+N22->null
}


fact {
	(QF.degree_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->i329+N0->i3210+N0->i3211+N0->i3212+N0->i3213+N0->i3214+N0->i3215+N0->i3216+N0->i3217+N0->i3218+N0->i3219+N0->i3220+N0->i3221+N0->i3222+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->i329+N1->i3210+N1->i3211+N1->i3212+N1->i3213+N1->i3214+N1->i3215+N1->i3216+N1->i3217+N1->i3218+N1->i3219+N1->i3220+N1->i3221+N1->i3222+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->i329+N2->i3210+N2->i3211+N2->i3212+N2->i3213+N2->i3214+N2->i3215+N2->i3216+N2->i3217+N2->i3218+N2->i3219+N2->i3220+N2->i3221+N2->i3222+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->i329+N3->i3210+N3->i3211+N3->i3212+N3->i3213+N3->i3214+N3->i3215+N3->i3216+N3->i3217+N3->i3218+N3->i3219+N3->i3220+N3->i3221+N3->i3222+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->i329+N4->i3210+N4->i3211+N4->i3212+N4->i3213+N4->i3214+N4->i3215+N4->i3216+N4->i3217+N4->i3218+N4->i3219+N4->i3220+N4->i3221+N4->i3222+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->i329+N5->i3210+N5->i3211+N5->i3212+N5->i3213+N5->i3214+N5->i3215+N5->i3216+N5->i3217+N5->i3218+N5->i3219+N5->i3220+N5->i3221+N5->i3222+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->i329+N6->i3210+N6->i3211+N6->i3212+N6->i3213+N6->i3214+N6->i3215+N6->i3216+N6->i3217+N6->i3218+N6->i3219+N6->i3220+N6->i3221+N6->i3222+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->i329+N7->i3210+N7->i3211+N7->i3212+N7->i3213+N7->i3214+N7->i3215+N7->i3216+N7->i3217+N7->i3218+N7->i3219+N7->i3220+N7->i3221+N7->i3222+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->i329+N8->i3210+N8->i3211+N8->i3212+N8->i3213+N8->i3214+N8->i3215+N8->i3216+N8->i3217+N8->i3218+N8->i3219+N8->i3220+N8->i3221+N8->i3222+N8->null+N9->i320+N9->i321+N9->i322+N9->i323+N9->i324+N9->i325+N9->i326+N9->i327+N9->i328+N9->i329+N9->i3210+N9->i3211+N9->i3212+N9->i3213+N9->i3214+N9->i3215+N9->i3216+N9->i3217+N9->i3218+N9->i3219+N9->i3220+N9->i3221+N9->i3222+N9->null+N10->i320+N10->i321+N10->i322+N10->i323+N10->i324+N10->i325+N10->i326+N10->i327+N10->i328+N10->i329+N10->i3210+N10->i3211+N10->i3212+N10->i3213+N10->i3214+N10->i3215+N10->i3216+N10->i3217+N10->i3218+N10->i3219+N10->i3220+N10->i3221+N10->i3222+N10->null+N11->i320+N11->i321+N11->i322+N11->i323+N11->i324+N11->i325+N11->i326+N11->i327+N11->i328+N11->i329+N11->i3210+N11->i3211+N11->i3212+N11->i3213+N11->i3214+N11->i3215+N11->i3216+N11->i3217+N11->i3218+N11->i3219+N11->i3220+N11->i3221+N11->i3222+N11->null+N12->i320+N12->i321+N12->i322+N12->i323+N12->i324+N12->i325+N12->i326+N12->i327+N12->i328+N12->i329+N12->i3210+N12->i3211+N12->i3212+N12->i3213+N12->i3214+N12->i3215+N12->i3216+N12->i3217+N12->i3218+N12->i3219+N12->i3220+N12->i3221+N12->i3222+N12->null+N13->i320+N13->i321+N13->i322+N13->i323+N13->i324+N13->i325+N13->i326+N13->i327+N13->i328+N13->i329+N13->i3210+N13->i3211+N13->i3212+N13->i3213+N13->i3214+N13->i3215+N13->i3216+N13->i3217+N13->i3218+N13->i3219+N13->i3220+N13->i3221+N13->i3222+N13->null+N14->i320+N14->i321+N14->i322+N14->i323+N14->i324+N14->i325+N14->i326+N14->i327+N14->i328+N14->i329+N14->i3210+N14->i3211+N14->i3212+N14->i3213+N14->i3214+N14->i3215+N14->i3216+N14->i3217+N14->i3218+N14->i3219+N14->i3220+N14->i3221+N14->i3222+N14->null+N15->i320+N15->i321+N15->i322+N15->i323+N15->i324+N15->i325+N15->i326+N15->i327+N15->i328+N15->i329+N15->i3210+N15->i3211+N15->i3212+N15->i3213+N15->i3214+N15->i3215+N15->i3216+N15->i3217+N15->i3218+N15->i3219+N15->i3220+N15->i3221+N15->i3222+N15->null+N16->i320+N16->i321+N16->i322+N16->i323+N16->i324+N16->i325+N16->i326+N16->i327+N16->i328+N16->i329+N16->i3210+N16->i3211+N16->i3212+N16->i3213+N16->i3214+N16->i3215+N16->i3216+N16->i3217+N16->i3218+N16->i3219+N16->i3220+N16->i3221+N16->i3222+N16->null+N17->i320+N17->i321+N17->i322+N17->i323+N17->i324+N17->i325+N17->i326+N17->i327+N17->i328+N17->i329+N17->i3210+N17->i3211+N17->i3212+N17->i3213+N17->i3214+N17->i3215+N17->i3216+N17->i3217+N17->i3218+N17->i3219+N17->i3220+N17->i3221+N17->i3222+N17->null+N18->i320+N18->i321+N18->i322+N18->i323+N18->i324+N18->i325+N18->i326+N18->i327+N18->i328+N18->i329+N18->i3210+N18->i3211+N18->i3212+N18->i3213+N18->i3214+N18->i3215+N18->i3216+N18->i3217+N18->i3218+N18->i3219+N18->i3220+N18->i3221+N18->i3222+N18->null+N19->i320+N19->i321+N19->i322+N19->i323+N19->i324+N19->i325+N19->i326+N19->i327+N19->i328+N19->i329+N19->i3210+N19->i3211+N19->i3212+N19->i3213+N19->i3214+N19->i3215+N19->i3216+N19->i3217+N19->i3218+N19->i3219+N19->i3220+N19->i3221+N19->i3222+N19->null+N20->i320+N20->i321+N20->i322+N20->i323+N20->i324+N20->i325+N20->i326+N20->i327+N20->i328+N20->i329+N20->i3210+N20->i3211+N20->i3212+N20->i3213+N20->i3214+N20->i3215+N20->i3216+N20->i3217+N20->i3218+N20->i3219+N20->i3220+N20->i3221+N20->i3222+N20->null+N21->i320+N21->i321+N21->i322+N21->i323+N21->i324+N21->i325+N21->i326+N21->i327+N21->i328+N21->i329+N21->i3210+N21->i3211+N21->i3212+N21->i3213+N21->i3214+N21->i3215+N21->i3216+N21->i3217+N21->i3218+N21->i3219+N21->i3220+N21->i3221+N21->i3222+N21->null+N22->i320+N22->i321+N22->i322+N22->i323+N22->i324+N22->i325+N22->i326+N22->i327+N22->i328+N22->i329+N22->i3210+N22->i3211+N22->i3212+N22->i3213+N22->i3214+N22->i3215+N22->i3216+N22->i3217+N22->i3218+N22->i3219+N22->i3220+N22->i3221+N22->i3222+N22->null
}


fact {
	(QF.size_0) in FibHeapIntVar->i320+FibHeapIntVar->i321+FibHeapIntVar->i322+FibHeapIntVar->i323+FibHeapIntVar->i324+FibHeapIntVar->i325+FibHeapIntVar->i326+FibHeapIntVar->i327+FibHeapIntVar->i328+FibHeapIntVar->i329+FibHeapIntVar->i3210+FibHeapIntVar->i3211+FibHeapIntVar->i3212+FibHeapIntVar->i3213+FibHeapIntVar->i3214+FibHeapIntVar->i3215+FibHeapIntVar->i3216+FibHeapIntVar->i3217+FibHeapIntVar->i3218+FibHeapIntVar->i3219+FibHeapIntVar->i3220+FibHeapIntVar->i3221+FibHeapIntVar->i3222+FibHeapIntVar->i3223
}




fun node_max[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22) {
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
   +
   N21->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)
   +
   N22->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21)
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
	  (m = N20 and size = i3221) or
	  (m = N21 and size = i3222) or
	  (m = N22 and size = i3223)
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

N14 in thiz.nodes.*(child + right) => (N14.child!=null => mysize114[(N14.child.*right - null),N14.degree])

N15 in thiz.nodes.*(child + right) => (N15.child!=null => mysize115[(N15.child.*right - null),N15.degree])

N16 in thiz.nodes.*(child + right) => (N16.child!=null => mysize116[(N16.child.*right - null),N16.degree])

N17 in thiz.nodes.*(child + right) => (N17.child!=null => mysize117[(N17.child.*right - null),N17.degree])

N18 in thiz.nodes.*(child + right) => (N18.child!=null => mysize118[(N18.child.*right - null),N18.degree])

N19 in thiz.nodes.*(child + right) => (N19.child!=null => mysize119[(N19.child.*right - null),N19.degree])

N20 in thiz.nodes.*(child + right) => (N20.child!=null => mysize120[(N20.child.*right - null),N20.degree])

N21 in thiz.nodes.*(child + right) => (N21.child!=null => mysize121[(N21.child.*right - null),N21.degree])

N22 in thiz.nodes.*(child + right) => (N22.child!=null => mysize122[(N22.child.*right - null),N22.degree])

}
}
one sig QF10 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

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
	 (QF10.x14 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13 and ((res = i3214 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14) or 
	 (QF10.x15 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14 and ((res = i3215 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15) or 
	 (QF10.x16 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15 and ((res = i3216 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16) or 
	 (QF10.x17 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16 and ((res = i3217 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17) or 
	 (QF10.x18 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17 and ((res = i3218 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18) or 
	 (QF10.x19 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18 and ((res = i3219 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18-QF10.x19) or 
	 (QF10.x20 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18-QF10.x19 and ((res = i3220 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18-QF10.x19-QF10.x20) or 
	 (QF10.x21 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18-QF10.x19-QF10.x20 and ((res = i3221 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18-QF10.x19-QF10.x20-QF10.x21) or 
	 (QF10.x22 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18-QF10.x19-QF10.x20-QF10.x21 and ((res = i3222 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18-QF10.x19-QF10.x20-QF10.x21-QF10.x22) or 
	 (QF10.x23 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18-QF10.x19-QF10.x20-QF10.x21-QF10.x22 and ((res = i3223 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18-QF10.x19-QF10.x20-QF10.x21-QF10.x22-QF10.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF11 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

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
	 (QF11.x14 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13 and ((res = i3214 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14) or 
	 (QF11.x15 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14 and ((res = i3215 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15) or 
	 (QF11.x16 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15 and ((res = i3216 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16) or 
	 (QF11.x17 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16 and ((res = i3217 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17) or 
	 (QF11.x18 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17 and ((res = i3218 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18) or 
	 (QF11.x19 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18 and ((res = i3219 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18-QF11.x19) or 
	 (QF11.x20 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18-QF11.x19 and ((res = i3220 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18-QF11.x19-QF11.x20) or 
	 (QF11.x21 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18-QF11.x19-QF11.x20 and ((res = i3221 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18-QF11.x19-QF11.x20-QF11.x21) or 
	 (QF11.x22 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18-QF11.x19-QF11.x20-QF11.x21 and ((res = i3222 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18-QF11.x19-QF11.x20-QF11.x21-QF11.x22) or 
	 (QF11.x23 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18-QF11.x19-QF11.x20-QF11.x21-QF11.x22 and ((res = i3223 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18-QF11.x19-QF11.x20-QF11.x21-QF11.x22-QF11.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF12 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

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
	 (QF12.x14 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13 and ((res = i3214 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14) or 
	 (QF12.x15 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14 and ((res = i3215 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15) or 
	 (QF12.x16 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15 and ((res = i3216 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16) or 
	 (QF12.x17 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16 and ((res = i3217 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17) or 
	 (QF12.x18 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17 and ((res = i3218 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18) or 
	 (QF12.x19 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18 and ((res = i3219 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18-QF12.x19) or 
	 (QF12.x20 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18-QF12.x19 and ((res = i3220 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18-QF12.x19-QF12.x20) or 
	 (QF12.x21 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18-QF12.x19-QF12.x20 and ((res = i3221 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18-QF12.x19-QF12.x20-QF12.x21) or 
	 (QF12.x22 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18-QF12.x19-QF12.x20-QF12.x21 and ((res = i3222 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18-QF12.x19-QF12.x20-QF12.x21-QF12.x22) or 
	 (QF12.x23 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18-QF12.x19-QF12.x20-QF12.x21-QF12.x22 and ((res = i3223 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18-QF12.x19-QF12.x20-QF12.x21-QF12.x22-QF12.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF13 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

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
	 (QF13.x14 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13 and ((res = i3214 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14) or 
	 (QF13.x15 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14 and ((res = i3215 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15) or 
	 (QF13.x16 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15 and ((res = i3216 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16) or 
	 (QF13.x17 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16 and ((res = i3217 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17) or 
	 (QF13.x18 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17 and ((res = i3218 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18) or 
	 (QF13.x19 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18 and ((res = i3219 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18-QF13.x19) or 
	 (QF13.x20 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18-QF13.x19 and ((res = i3220 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18-QF13.x19-QF13.x20) or 
	 (QF13.x21 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18-QF13.x19-QF13.x20 and ((res = i3221 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18-QF13.x19-QF13.x20-QF13.x21) or 
	 (QF13.x22 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18-QF13.x19-QF13.x20-QF13.x21 and ((res = i3222 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18-QF13.x19-QF13.x20-QF13.x21-QF13.x22) or 
	 (QF13.x23 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18-QF13.x19-QF13.x20-QF13.x21-QF13.x22 and ((res = i3223 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18-QF13.x19-QF13.x20-QF13.x21-QF13.x22-QF13.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF14 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

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
	 (QF14.x14 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13 and ((res = i3214 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14) or 
	 (QF14.x15 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14 and ((res = i3215 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15) or 
	 (QF14.x16 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15 and ((res = i3216 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16) or 
	 (QF14.x17 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16 and ((res = i3217 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17) or 
	 (QF14.x18 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17 and ((res = i3218 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18) or 
	 (QF14.x19 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18 and ((res = i3219 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18-QF14.x19) or 
	 (QF14.x20 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18-QF14.x19 and ((res = i3220 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18-QF14.x19-QF14.x20) or 
	 (QF14.x21 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18-QF14.x19-QF14.x20 and ((res = i3221 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18-QF14.x19-QF14.x20-QF14.x21) or 
	 (QF14.x22 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18-QF14.x19-QF14.x20-QF14.x21 and ((res = i3222 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18-QF14.x19-QF14.x20-QF14.x21-QF14.x22) or 
	 (QF14.x23 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18-QF14.x19-QF14.x20-QF14.x21-QF14.x22 and ((res = i3223 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18-QF14.x19-QF14.x20-QF14.x21-QF14.x22-QF14.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF15 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

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
	 (QF15.x14 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13 and ((res = i3214 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14) or 
	 (QF15.x15 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14 and ((res = i3215 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15) or 
	 (QF15.x16 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15 and ((res = i3216 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16) or 
	 (QF15.x17 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16 and ((res = i3217 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17) or 
	 (QF15.x18 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17 and ((res = i3218 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18) or 
	 (QF15.x19 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18 and ((res = i3219 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18-QF15.x19) or 
	 (QF15.x20 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18-QF15.x19 and ((res = i3220 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18-QF15.x19-QF15.x20) or 
	 (QF15.x21 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18-QF15.x19-QF15.x20 and ((res = i3221 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18-QF15.x19-QF15.x20-QF15.x21) or 
	 (QF15.x22 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18-QF15.x19-QF15.x20-QF15.x21 and ((res = i3222 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18-QF15.x19-QF15.x20-QF15.x21-QF15.x22) or 
	 (QF15.x23 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18-QF15.x19-QF15.x20-QF15.x21-QF15.x22 and ((res = i3223 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18-QF15.x19-QF15.x20-QF15.x21-QF15.x22-QF15.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF16 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

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
	 (QF16.x14 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13 and ((res = i3214 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14) or 
	 (QF16.x15 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14 and ((res = i3215 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15) or 
	 (QF16.x16 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15 and ((res = i3216 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16) or 
	 (QF16.x17 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16 and ((res = i3217 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17) or 
	 (QF16.x18 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17 and ((res = i3218 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18) or 
	 (QF16.x19 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18 and ((res = i3219 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18-QF16.x19) or 
	 (QF16.x20 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18-QF16.x19 and ((res = i3220 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18-QF16.x19-QF16.x20) or 
	 (QF16.x21 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18-QF16.x19-QF16.x20 and ((res = i3221 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18-QF16.x19-QF16.x20-QF16.x21) or 
	 (QF16.x22 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18-QF16.x19-QF16.x20-QF16.x21 and ((res = i3222 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18-QF16.x19-QF16.x20-QF16.x21-QF16.x22) or 
	 (QF16.x23 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18-QF16.x19-QF16.x20-QF16.x21-QF16.x22 and ((res = i3223 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18-QF16.x19-QF16.x20-QF16.x21-QF16.x22-QF16.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF17 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

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
	 (QF17.x14 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13 and ((res = i3214 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14) or 
	 (QF17.x15 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14 and ((res = i3215 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15) or 
	 (QF17.x16 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15 and ((res = i3216 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16) or 
	 (QF17.x17 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16 and ((res = i3217 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17) or 
	 (QF17.x18 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17 and ((res = i3218 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18) or 
	 (QF17.x19 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18 and ((res = i3219 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18-QF17.x19) or 
	 (QF17.x20 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18-QF17.x19 and ((res = i3220 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18-QF17.x19-QF17.x20) or 
	 (QF17.x21 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18-QF17.x19-QF17.x20 and ((res = i3221 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18-QF17.x19-QF17.x20-QF17.x21) or 
	 (QF17.x22 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18-QF17.x19-QF17.x20-QF17.x21 and ((res = i3222 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18-QF17.x19-QF17.x20-QF17.x21-QF17.x22) or 
	 (QF17.x23 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18-QF17.x19-QF17.x20-QF17.x21-QF17.x22 and ((res = i3223 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18-QF17.x19-QF17.x20-QF17.x21-QF17.x22-QF17.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF18 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

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
	 (QF18.x14 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13 and ((res = i3214 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14) or 
	 (QF18.x15 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14 and ((res = i3215 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15) or 
	 (QF18.x16 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15 and ((res = i3216 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16) or 
	 (QF18.x17 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16 and ((res = i3217 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17) or 
	 (QF18.x18 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17 and ((res = i3218 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18) or 
	 (QF18.x19 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18 and ((res = i3219 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18-QF18.x19) or 
	 (QF18.x20 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18-QF18.x19 and ((res = i3220 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18-QF18.x19-QF18.x20) or 
	 (QF18.x21 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18-QF18.x19-QF18.x20 and ((res = i3221 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18-QF18.x19-QF18.x20-QF18.x21) or 
	 (QF18.x22 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18-QF18.x19-QF18.x20-QF18.x21 and ((res = i3222 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18-QF18.x19-QF18.x20-QF18.x21-QF18.x22) or 
	 (QF18.x23 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18-QF18.x19-QF18.x20-QF18.x21-QF18.x22 and ((res = i3223 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18-QF18.x19-QF18.x20-QF18.x21-QF18.x22-QF18.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF19 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

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
	 (QF19.x14 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13 and ((res = i3214 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14) or 
	 (QF19.x15 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14 and ((res = i3215 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15) or 
	 (QF19.x16 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15 and ((res = i3216 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16) or 
	 (QF19.x17 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16 and ((res = i3217 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17) or 
	 (QF19.x18 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17 and ((res = i3218 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18) or 
	 (QF19.x19 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18 and ((res = i3219 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18-QF19.x19) or 
	 (QF19.x20 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18-QF19.x19 and ((res = i3220 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18-QF19.x19-QF19.x20) or 
	 (QF19.x21 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18-QF19.x19-QF19.x20 and ((res = i3221 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18-QF19.x19-QF19.x20-QF19.x21) or 
	 (QF19.x22 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18-QF19.x19-QF19.x20-QF19.x21 and ((res = i3222 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18-QF19.x19-QF19.x20-QF19.x21-QF19.x22) or 
	 (QF19.x23 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18-QF19.x19-QF19.x20-QF19.x21-QF19.x22 and ((res = i3223 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18-QF19.x19-QF19.x20-QF19.x21-QF19.x22-QF19.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF110 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

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
	 (QF110.x14 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13 and ((res = i3214 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14) or 
	 (QF110.x15 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14 and ((res = i3215 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15) or 
	 (QF110.x16 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15 and ((res = i3216 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16) or 
	 (QF110.x17 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16 and ((res = i3217 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17) or 
	 (QF110.x18 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17 and ((res = i3218 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18) or 
	 (QF110.x19 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18 and ((res = i3219 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18-QF110.x19) or 
	 (QF110.x20 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18-QF110.x19 and ((res = i3220 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18-QF110.x19-QF110.x20) or 
	 (QF110.x21 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18-QF110.x19-QF110.x20 and ((res = i3221 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18-QF110.x19-QF110.x20-QF110.x21) or 
	 (QF110.x22 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18-QF110.x19-QF110.x20-QF110.x21 and ((res = i3222 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18-QF110.x19-QF110.x20-QF110.x21-QF110.x22) or 
	 (QF110.x23 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18-QF110.x19-QF110.x20-QF110.x21-QF110.x22 and ((res = i3223 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18-QF110.x19-QF110.x20-QF110.x21-QF110.x22-QF110.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF111 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

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
	 (QF111.x14 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13 and ((res = i3214 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14) or 
	 (QF111.x15 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14 and ((res = i3215 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15) or 
	 (QF111.x16 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15 and ((res = i3216 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16) or 
	 (QF111.x17 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16 and ((res = i3217 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17) or 
	 (QF111.x18 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17 and ((res = i3218 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18) or 
	 (QF111.x19 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18 and ((res = i3219 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18-QF111.x19) or 
	 (QF111.x20 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18-QF111.x19 and ((res = i3220 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18-QF111.x19-QF111.x20) or 
	 (QF111.x21 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18-QF111.x19-QF111.x20 and ((res = i3221 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18-QF111.x19-QF111.x20-QF111.x21) or 
	 (QF111.x22 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18-QF111.x19-QF111.x20-QF111.x21 and ((res = i3222 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18-QF111.x19-QF111.x20-QF111.x21-QF111.x22) or 
	 (QF111.x23 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18-QF111.x19-QF111.x20-QF111.x21-QF111.x22 and ((res = i3223 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18-QF111.x19-QF111.x20-QF111.x21-QF111.x22-QF111.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF112 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

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
	 (QF112.x14 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13 and ((res = i3214 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14) or 
	 (QF112.x15 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14 and ((res = i3215 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15) or 
	 (QF112.x16 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15 and ((res = i3216 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16) or 
	 (QF112.x17 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16 and ((res = i3217 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17) or 
	 (QF112.x18 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17 and ((res = i3218 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18) or 
	 (QF112.x19 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18 and ((res = i3219 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18-QF112.x19) or 
	 (QF112.x20 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18-QF112.x19 and ((res = i3220 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18-QF112.x19-QF112.x20) or 
	 (QF112.x21 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18-QF112.x19-QF112.x20 and ((res = i3221 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18-QF112.x19-QF112.x20-QF112.x21) or 
	 (QF112.x22 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18-QF112.x19-QF112.x20-QF112.x21 and ((res = i3222 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18-QF112.x19-QF112.x20-QF112.x21-QF112.x22) or 
	 (QF112.x23 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18-QF112.x19-QF112.x20-QF112.x21-QF112.x22 and ((res = i3223 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18-QF112.x19-QF112.x20-QF112.x21-QF112.x22-QF112.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF113 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

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
	 (QF113.x14 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13 and ((res = i3214 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14) or 
	 (QF113.x15 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14 and ((res = i3215 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15) or 
	 (QF113.x16 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15 and ((res = i3216 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16) or 
	 (QF113.x17 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16 and ((res = i3217 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17) or 
	 (QF113.x18 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17 and ((res = i3218 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18) or 
	 (QF113.x19 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18 and ((res = i3219 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18-QF113.x19) or 
	 (QF113.x20 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18-QF113.x19 and ((res = i3220 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18-QF113.x19-QF113.x20) or 
	 (QF113.x21 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18-QF113.x19-QF113.x20 and ((res = i3221 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18-QF113.x19-QF113.x20-QF113.x21) or 
	 (QF113.x22 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18-QF113.x19-QF113.x20-QF113.x21 and ((res = i3222 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18-QF113.x19-QF113.x20-QF113.x21-QF113.x22) or 
	 (QF113.x23 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18-QF113.x19-QF113.x20-QF113.x21-QF113.x22 and ((res = i3223 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18-QF113.x19-QF113.x20-QF113.x21-QF113.x22-QF113.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF114 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

pred mysize114[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF114.x20 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16-QF114.x17-QF114.x18-QF114.x19 and ((res = i3220 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16-QF114.x17-QF114.x18-QF114.x19-QF114.x20) or 
	 (QF114.x21 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16-QF114.x17-QF114.x18-QF114.x19-QF114.x20 and ((res = i3221 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16-QF114.x17-QF114.x18-QF114.x19-QF114.x20-QF114.x21) or 
	 (QF114.x22 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16-QF114.x17-QF114.x18-QF114.x19-QF114.x20-QF114.x21 and ((res = i3222 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16-QF114.x17-QF114.x18-QF114.x19-QF114.x20-QF114.x21-QF114.x22) or 
	 (QF114.x23 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16-QF114.x17-QF114.x18-QF114.x19-QF114.x20-QF114.x21-QF114.x22 and ((res = i3223 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16-QF114.x17-QF114.x18-QF114.x19-QF114.x20-QF114.x21-QF114.x22-QF114.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF115 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

pred mysize115[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF115.x20 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16-QF115.x17-QF115.x18-QF115.x19 and ((res = i3220 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16-QF115.x17-QF115.x18-QF115.x19-QF115.x20) or 
	 (QF115.x21 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16-QF115.x17-QF115.x18-QF115.x19-QF115.x20 and ((res = i3221 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16-QF115.x17-QF115.x18-QF115.x19-QF115.x20-QF115.x21) or 
	 (QF115.x22 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16-QF115.x17-QF115.x18-QF115.x19-QF115.x20-QF115.x21 and ((res = i3222 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16-QF115.x17-QF115.x18-QF115.x19-QF115.x20-QF115.x21-QF115.x22) or 
	 (QF115.x23 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16-QF115.x17-QF115.x18-QF115.x19-QF115.x20-QF115.x21-QF115.x22 and ((res = i3223 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16-QF115.x17-QF115.x18-QF115.x19-QF115.x20-QF115.x21-QF115.x22-QF115.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF116 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

pred mysize116[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF116.x20 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16-QF116.x17-QF116.x18-QF116.x19 and ((res = i3220 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16-QF116.x17-QF116.x18-QF116.x19-QF116.x20) or 
	 (QF116.x21 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16-QF116.x17-QF116.x18-QF116.x19-QF116.x20 and ((res = i3221 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16-QF116.x17-QF116.x18-QF116.x19-QF116.x20-QF116.x21) or 
	 (QF116.x22 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16-QF116.x17-QF116.x18-QF116.x19-QF116.x20-QF116.x21 and ((res = i3222 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16-QF116.x17-QF116.x18-QF116.x19-QF116.x20-QF116.x21-QF116.x22) or 
	 (QF116.x23 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16-QF116.x17-QF116.x18-QF116.x19-QF116.x20-QF116.x21-QF116.x22 and ((res = i3223 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16-QF116.x17-QF116.x18-QF116.x19-QF116.x20-QF116.x21-QF116.x22-QF116.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF117 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

pred mysize117[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF117.x20 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16-QF117.x17-QF117.x18-QF117.x19 and ((res = i3220 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16-QF117.x17-QF117.x18-QF117.x19-QF117.x20) or 
	 (QF117.x21 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16-QF117.x17-QF117.x18-QF117.x19-QF117.x20 and ((res = i3221 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16-QF117.x17-QF117.x18-QF117.x19-QF117.x20-QF117.x21) or 
	 (QF117.x22 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16-QF117.x17-QF117.x18-QF117.x19-QF117.x20-QF117.x21 and ((res = i3222 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16-QF117.x17-QF117.x18-QF117.x19-QF117.x20-QF117.x21-QF117.x22) or 
	 (QF117.x23 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16-QF117.x17-QF117.x18-QF117.x19-QF117.x20-QF117.x21-QF117.x22 and ((res = i3223 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16-QF117.x17-QF117.x18-QF117.x19-QF117.x20-QF117.x21-QF117.x22-QF117.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF118 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

pred mysize118[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF118.x20 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16-QF118.x17-QF118.x18-QF118.x19 and ((res = i3220 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16-QF118.x17-QF118.x18-QF118.x19-QF118.x20) or 
	 (QF118.x21 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16-QF118.x17-QF118.x18-QF118.x19-QF118.x20 and ((res = i3221 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16-QF118.x17-QF118.x18-QF118.x19-QF118.x20-QF118.x21) or 
	 (QF118.x22 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16-QF118.x17-QF118.x18-QF118.x19-QF118.x20-QF118.x21 and ((res = i3222 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16-QF118.x17-QF118.x18-QF118.x19-QF118.x20-QF118.x21-QF118.x22) or 
	 (QF118.x23 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16-QF118.x17-QF118.x18-QF118.x19-QF118.x20-QF118.x21-QF118.x22 and ((res = i3223 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16-QF118.x17-QF118.x18-QF118.x19-QF118.x20-QF118.x21-QF118.x22-QF118.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF119 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

pred mysize119[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF119.x20 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16-QF119.x17-QF119.x18-QF119.x19 and ((res = i3220 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16-QF119.x17-QF119.x18-QF119.x19-QF119.x20) or 
	 (QF119.x21 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16-QF119.x17-QF119.x18-QF119.x19-QF119.x20 and ((res = i3221 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16-QF119.x17-QF119.x18-QF119.x19-QF119.x20-QF119.x21) or 
	 (QF119.x22 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16-QF119.x17-QF119.x18-QF119.x19-QF119.x20-QF119.x21 and ((res = i3222 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16-QF119.x17-QF119.x18-QF119.x19-QF119.x20-QF119.x21-QF119.x22) or 
	 (QF119.x23 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16-QF119.x17-QF119.x18-QF119.x19-QF119.x20-QF119.x21-QF119.x22 and ((res = i3223 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16-QF119.x17-QF119.x18-QF119.x19-QF119.x20-QF119.x21-QF119.x22-QF119.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF120 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

pred mysize120[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF120.x1 in s and ((res = i321 and no s-QF120.x1) or 
	 (QF120.x2 in s-QF120.x1 and ((res = i322 and no s-QF120.x1-QF120.x2) or 
	 (QF120.x3 in s-QF120.x1-QF120.x2 and ((res = i323 and no s-QF120.x1-QF120.x2-QF120.x3) or 
	 (QF120.x4 in s-QF120.x1-QF120.x2-QF120.x3 and ((res = i324 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4) or 
	 (QF120.x5 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4 and ((res = i325 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5) or 
	 (QF120.x6 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5 and ((res = i326 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6) or 
	 (QF120.x7 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6 and ((res = i327 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7) or 
	 (QF120.x8 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7 and ((res = i328 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8) or 
	 (QF120.x9 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8 and ((res = i329 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9) or 
	 (QF120.x10 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9 and ((res = i3210 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10) or 
	 (QF120.x11 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10 and ((res = i3211 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11) or 
	 (QF120.x12 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11 and ((res = i3212 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12) or 
	 (QF120.x13 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12 and ((res = i3213 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13) or 
	 (QF120.x14 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13 and ((res = i3214 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14) or 
	 (QF120.x15 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14 and ((res = i3215 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15) or 
	 (QF120.x16 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15 and ((res = i3216 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15-QF120.x16) or 
	 (QF120.x17 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15-QF120.x16 and ((res = i3217 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15-QF120.x16-QF120.x17) or 
	 (QF120.x18 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15-QF120.x16-QF120.x17 and ((res = i3218 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15-QF120.x16-QF120.x17-QF120.x18) or 
	 (QF120.x19 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15-QF120.x16-QF120.x17-QF120.x18 and ((res = i3219 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15-QF120.x16-QF120.x17-QF120.x18-QF120.x19) or 
	 (QF120.x20 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15-QF120.x16-QF120.x17-QF120.x18-QF120.x19 and ((res = i3220 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15-QF120.x16-QF120.x17-QF120.x18-QF120.x19-QF120.x20) or 
	 (QF120.x21 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15-QF120.x16-QF120.x17-QF120.x18-QF120.x19-QF120.x20 and ((res = i3221 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15-QF120.x16-QF120.x17-QF120.x18-QF120.x19-QF120.x20-QF120.x21) or 
	 (QF120.x22 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15-QF120.x16-QF120.x17-QF120.x18-QF120.x19-QF120.x20-QF120.x21 and ((res = i3222 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15-QF120.x16-QF120.x17-QF120.x18-QF120.x19-QF120.x20-QF120.x21-QF120.x22) or 
	 (QF120.x23 in s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15-QF120.x16-QF120.x17-QF120.x18-QF120.x19-QF120.x20-QF120.x21-QF120.x22 and ((res = i3223 and no s-QF120.x1-QF120.x2-QF120.x3-QF120.x4-QF120.x5-QF120.x6-QF120.x7-QF120.x8-QF120.x9-QF120.x10-QF120.x11-QF120.x12-QF120.x13-QF120.x14-QF120.x15-QF120.x16-QF120.x17-QF120.x18-QF120.x19-QF120.x20-QF120.x21-QF120.x22-QF120.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF121 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

pred mysize121[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF121.x1 in s and ((res = i321 and no s-QF121.x1) or 
	 (QF121.x2 in s-QF121.x1 and ((res = i322 and no s-QF121.x1-QF121.x2) or 
	 (QF121.x3 in s-QF121.x1-QF121.x2 and ((res = i323 and no s-QF121.x1-QF121.x2-QF121.x3) or 
	 (QF121.x4 in s-QF121.x1-QF121.x2-QF121.x3 and ((res = i324 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4) or 
	 (QF121.x5 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4 and ((res = i325 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5) or 
	 (QF121.x6 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5 and ((res = i326 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6) or 
	 (QF121.x7 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6 and ((res = i327 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7) or 
	 (QF121.x8 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7 and ((res = i328 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8) or 
	 (QF121.x9 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8 and ((res = i329 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9) or 
	 (QF121.x10 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9 and ((res = i3210 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10) or 
	 (QF121.x11 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10 and ((res = i3211 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11) or 
	 (QF121.x12 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11 and ((res = i3212 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12) or 
	 (QF121.x13 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12 and ((res = i3213 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13) or 
	 (QF121.x14 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13 and ((res = i3214 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14) or 
	 (QF121.x15 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14 and ((res = i3215 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15) or 
	 (QF121.x16 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15 and ((res = i3216 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15-QF121.x16) or 
	 (QF121.x17 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15-QF121.x16 and ((res = i3217 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15-QF121.x16-QF121.x17) or 
	 (QF121.x18 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15-QF121.x16-QF121.x17 and ((res = i3218 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15-QF121.x16-QF121.x17-QF121.x18) or 
	 (QF121.x19 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15-QF121.x16-QF121.x17-QF121.x18 and ((res = i3219 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15-QF121.x16-QF121.x17-QF121.x18-QF121.x19) or 
	 (QF121.x20 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15-QF121.x16-QF121.x17-QF121.x18-QF121.x19 and ((res = i3220 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15-QF121.x16-QF121.x17-QF121.x18-QF121.x19-QF121.x20) or 
	 (QF121.x21 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15-QF121.x16-QF121.x17-QF121.x18-QF121.x19-QF121.x20 and ((res = i3221 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15-QF121.x16-QF121.x17-QF121.x18-QF121.x19-QF121.x20-QF121.x21) or 
	 (QF121.x22 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15-QF121.x16-QF121.x17-QF121.x18-QF121.x19-QF121.x20-QF121.x21 and ((res = i3222 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15-QF121.x16-QF121.x17-QF121.x18-QF121.x19-QF121.x20-QF121.x21-QF121.x22) or 
	 (QF121.x23 in s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15-QF121.x16-QF121.x17-QF121.x18-QF121.x19-QF121.x20-QF121.x21-QF121.x22 and ((res = i3223 and no s-QF121.x1-QF121.x2-QF121.x3-QF121.x4-QF121.x5-QF121.x6-QF121.x7-QF121.x8-QF121.x9-QF121.x10-QF121.x11-QF121.x12-QF121.x13-QF121.x14-QF121.x15-QF121.x16-QF121.x17-QF121.x18-QF121.x19-QF121.x20-QF121.x21-QF121.x22-QF121.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}
one sig QF122 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode,x15:FibHeapIntVarNode,x16:FibHeapIntVarNode,x17:FibHeapIntVarNode,x18:FibHeapIntVarNode,x19:FibHeapIntVarNode,x20:FibHeapIntVarNode,x21:FibHeapIntVarNode,x22:FibHeapIntVarNode,x23:FibHeapIntVarNode }

pred mysize122[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF122.x1 in s and ((res = i321 and no s-QF122.x1) or 
	 (QF122.x2 in s-QF122.x1 and ((res = i322 and no s-QF122.x1-QF122.x2) or 
	 (QF122.x3 in s-QF122.x1-QF122.x2 and ((res = i323 and no s-QF122.x1-QF122.x2-QF122.x3) or 
	 (QF122.x4 in s-QF122.x1-QF122.x2-QF122.x3 and ((res = i324 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4) or 
	 (QF122.x5 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4 and ((res = i325 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5) or 
	 (QF122.x6 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5 and ((res = i326 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6) or 
	 (QF122.x7 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6 and ((res = i327 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7) or 
	 (QF122.x8 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7 and ((res = i328 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8) or 
	 (QF122.x9 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8 and ((res = i329 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9) or 
	 (QF122.x10 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9 and ((res = i3210 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10) or 
	 (QF122.x11 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10 and ((res = i3211 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11) or 
	 (QF122.x12 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11 and ((res = i3212 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12) or 
	 (QF122.x13 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12 and ((res = i3213 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13) or 
	 (QF122.x14 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13 and ((res = i3214 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14) or 
	 (QF122.x15 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14 and ((res = i3215 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15) or 
	 (QF122.x16 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15 and ((res = i3216 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15-QF122.x16) or 
	 (QF122.x17 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15-QF122.x16 and ((res = i3217 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15-QF122.x16-QF122.x17) or 
	 (QF122.x18 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15-QF122.x16-QF122.x17 and ((res = i3218 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15-QF122.x16-QF122.x17-QF122.x18) or 
	 (QF122.x19 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15-QF122.x16-QF122.x17-QF122.x18 and ((res = i3219 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15-QF122.x16-QF122.x17-QF122.x18-QF122.x19) or 
	 (QF122.x20 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15-QF122.x16-QF122.x17-QF122.x18-QF122.x19 and ((res = i3220 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15-QF122.x16-QF122.x17-QF122.x18-QF122.x19-QF122.x20) or 
	 (QF122.x21 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15-QF122.x16-QF122.x17-QF122.x18-QF122.x19-QF122.x20 and ((res = i3221 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15-QF122.x16-QF122.x17-QF122.x18-QF122.x19-QF122.x20-QF122.x21) or 
	 (QF122.x22 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15-QF122.x16-QF122.x17-QF122.x18-QF122.x19-QF122.x20-QF122.x21 and ((res = i3222 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15-QF122.x16-QF122.x17-QF122.x18-QF122.x19-QF122.x20-QF122.x21-QF122.x22) or 
	 (QF122.x23 in s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15-QF122.x16-QF122.x17-QF122.x18-QF122.x19-QF122.x20-QF122.x21-QF122.x22 and ((res = i3223 and no s-QF122.x1-QF122.x2-QF122.x3-QF122.x4-QF122.x5-QF122.x6-QF122.x7-QF122.x8-QF122.x9-QF122.x10-QF122.x11-QF122.x12-QF122.x13-QF122.x14-QF122.x15-QF122.x16-QF122.x17-QF122.x18-QF122.x19-QF122.x20-QF122.x21-QF122.x22-QF122.x23)
	))))))))))))))))))))))))))))))))))))))))))))))
}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 FibHeapIntVar, exactly 23 FibHeapIntVarNode, 1 int, exactly 24 JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22) -> lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22) {
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
 +
 N20->N21
 +
 N21->N22
}


fun node_prevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22) {
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
   +
   N21->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)
   +
   N22->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21)
 )
}


fun node_rprevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22) {
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
   +
   N21->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21)
   +
   N22->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
 )
}


fun node_relprevs[] : (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22) -> set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22) {
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
   +
   N21->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21)
   +
   N22->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
}


fun node_min[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22) {
 es - es.(
   N0->(N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N1->(N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N2->(N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N3->(N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N4->(N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N5->(N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N6->(N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N7->(N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N8->(N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N9->(N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N10->(N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N11->(N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N12->(N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N13->(N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N14->(N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N15->(N16+N17+N18+N19+N20+N21+N22)
   +
   N16->(N17+N18+N19+N20+N21+N22)
   +
   N17->(N18+N19+N20+N21+N22)
   +
   N18->(N19+N20+N21+N22)
   +
   N19->(N20+N21+N22)
   +
   N20->(N21+N22)
   +
   N21->(N22)
 )
}




