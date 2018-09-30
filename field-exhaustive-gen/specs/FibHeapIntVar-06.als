module fibheapintvar 

open Integer4

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



fun FReach[] : set (N0+N1+N2+N3+N4+N5) {
  (QF.thiz_0).(QF.nodes_0).*(QF.fchild_0 + QF.fright_0) - null
}
one sig N0,N1,N2,N3,N4,N5 extends FibHeapIntVarNode {}


one sig i320,i321,i322,i323,i324,i325,i326 extends JavaPrimitiveIntegerValue {} 
fact {
	// int32 bounds 
	b01 in i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true
	i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true in b01
	b00 in i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false
	i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false in b00
	b03 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false in b03
	b02 in i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true
	i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true in b02
}



fact { QF.fright_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->null+N2->N3+N2->N4+N2->N5+N2->null+N3->N4+N3->N5+N3->null+N4->N5+N4->null+N5->null }
fact { QF.fleft_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->null+N2->N3+N2->N4+N2->N5+N2->null+N3->N4+N3->N5+N3->null+N4->N5+N4->null+N5->null }
fact { QF.fchild_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->null+N2->N3+N2->N4+N2->N5+N2->null+N3->N4+N3->N5+N3->null+N4->N5+N4->null+N5->null }
fact { QF.fparent_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->null+N2->N3+N2->N4+N2->N5+N2->null+N3->N4+N3->N5+N3->null+N4->N5+N4->null+N5->null }
fact { QF.bright_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5 }
fact { QF.bleft_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5 }
fact { QF.bchild_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5 }
fact { QF.bparent_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5 }


fact {
	(QF.key_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->null
}


fact {
	(QF.degree_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->null
}


fact {
	(QF.size_0) in FibHeapIntVar->i320+FibHeapIntVar->i321+FibHeapIntVar->i322+FibHeapIntVar->i323+FibHeapIntVar->i324+FibHeapIntVar->i325+FibHeapIntVar->i326
}




fun node_max[es: set (N0+N1+N2+N3+N4+N5)] : lone (N0+N1+N2+N3+N4+N5) {
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
	  (m = N5 and size = i326)
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

}
}
one sig QF10 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode }

pred mysize10[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF10.x1 in s and ((res = i321 and no s-QF10.x1) or 
	 (QF10.x2 in s-QF10.x1 and ((res = i322 and no s-QF10.x1-QF10.x2) or 
	 (QF10.x3 in s-QF10.x1-QF10.x2 and ((res = i323 and no s-QF10.x1-QF10.x2-QF10.x3) or 
	 (QF10.x4 in s-QF10.x1-QF10.x2-QF10.x3 and ((res = i324 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4) or 
	 (QF10.x5 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4 and ((res = i325 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5) or 
	 (QF10.x6 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5 and ((res = i326 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6)
	))))))))))))
}
one sig QF11 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode }

pred mysize11[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF11.x1 in s and ((res = i321 and no s-QF11.x1) or 
	 (QF11.x2 in s-QF11.x1 and ((res = i322 and no s-QF11.x1-QF11.x2) or 
	 (QF11.x3 in s-QF11.x1-QF11.x2 and ((res = i323 and no s-QF11.x1-QF11.x2-QF11.x3) or 
	 (QF11.x4 in s-QF11.x1-QF11.x2-QF11.x3 and ((res = i324 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4) or 
	 (QF11.x5 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4 and ((res = i325 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5) or 
	 (QF11.x6 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5 and ((res = i326 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6)
	))))))))))))
}
one sig QF12 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode }

pred mysize12[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF12.x1 in s and ((res = i321 and no s-QF12.x1) or 
	 (QF12.x2 in s-QF12.x1 and ((res = i322 and no s-QF12.x1-QF12.x2) or 
	 (QF12.x3 in s-QF12.x1-QF12.x2 and ((res = i323 and no s-QF12.x1-QF12.x2-QF12.x3) or 
	 (QF12.x4 in s-QF12.x1-QF12.x2-QF12.x3 and ((res = i324 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4) or 
	 (QF12.x5 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4 and ((res = i325 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5) or 
	 (QF12.x6 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5 and ((res = i326 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6)
	))))))))))))
}
one sig QF13 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode }

pred mysize13[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF13.x1 in s and ((res = i321 and no s-QF13.x1) or 
	 (QF13.x2 in s-QF13.x1 and ((res = i322 and no s-QF13.x1-QF13.x2) or 
	 (QF13.x3 in s-QF13.x1-QF13.x2 and ((res = i323 and no s-QF13.x1-QF13.x2-QF13.x3) or 
	 (QF13.x4 in s-QF13.x1-QF13.x2-QF13.x3 and ((res = i324 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4) or 
	 (QF13.x5 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4 and ((res = i325 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5) or 
	 (QF13.x6 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5 and ((res = i326 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6)
	))))))))))))
}
one sig QF14 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode }

pred mysize14[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF14.x1 in s and ((res = i321 and no s-QF14.x1) or 
	 (QF14.x2 in s-QF14.x1 and ((res = i322 and no s-QF14.x1-QF14.x2) or 
	 (QF14.x3 in s-QF14.x1-QF14.x2 and ((res = i323 and no s-QF14.x1-QF14.x2-QF14.x3) or 
	 (QF14.x4 in s-QF14.x1-QF14.x2-QF14.x3 and ((res = i324 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4) or 
	 (QF14.x5 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4 and ((res = i325 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5) or 
	 (QF14.x6 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5 and ((res = i326 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6)
	))))))))))))
}
one sig QF15 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode }

pred mysize15[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF15.x1 in s and ((res = i321 and no s-QF15.x1) or 
	 (QF15.x2 in s-QF15.x1 and ((res = i322 and no s-QF15.x1-QF15.x2) or 
	 (QF15.x3 in s-QF15.x1-QF15.x2 and ((res = i323 and no s-QF15.x1-QF15.x2-QF15.x3) or 
	 (QF15.x4 in s-QF15.x1-QF15.x2-QF15.x3 and ((res = i324 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4) or 
	 (QF15.x5 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4 and ((res = i325 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5) or 
	 (QF15.x6 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5 and ((res = i326 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6)
	))))))))))))
}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 FibHeapIntVar, exactly 6 FibHeapIntVarNode, 1 int, exactly 7 JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2+N3+N4+N5) -> lone (N0+N1+N2+N3+N4+N5) {
 N0->N1
 +
 N1->N2
 +
 N2->N3
 +
 N3->N4
 +
 N4->N5
}


fun node_prevs[e: N0+N1+N2+N3+N4+N5] :set (N0+N1+N2+N3+N4+N5) {
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
 )
}


fun node_rprevs[e: N0+N1+N2+N3+N4+N5] :set (N0+N1+N2+N3+N4+N5) {
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
 )
}


fun node_relprevs[] : (N0+N1+N2+N3+N4+N5) -> set (N0+N1+N2+N3+N4+N5) {
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
}


fun node_min[es: set (N0+N1+N2+N3+N4+N5)] : lone (N0+N1+N2+N3+N4+N5) {
 es - es.(
   N0->(N1+N2+N3+N4+N5)
   +
   N1->(N2+N3+N4+N5)
   +
   N2->(N3+N4+N5)
   +
   N3->(N4+N5)
   +
   N4->(N5)
 )
}




