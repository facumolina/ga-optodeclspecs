module bstreeintvar

open Integer4

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
   N0+N1+N2+N3+N4+N5 = ff1.univ + bf1.univ   
   N0+N1+N2+N3+N4+N5 = ff2.univ + bf2.univ   

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


fun FReach[] :set (N0+N1+N2+N3+N4+N5) {
    (QF.thiz_0).(QF.root_0).*(QF.fleft_0 + QF.fright_0) - null
}

one sig N0,N1,N2,N3,N4,N5 extends BSTreeIntVarNode {}


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



fact { QF.fleft_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->null+N2->N3+N2->N4+N2->N5+N2->null+N3->N4+N3->N5+N3->null+N4->N5+N4->null+N5->null }
fact { QF.fright_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->null+N2->N3+N2->N4+N2->N5+N2->null+N3->N4+N3->N5+N3->null+N4->N5+N4->null+N5->null }
fact { QF.bleft_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5 }
fact { QF.bright_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5 }


fact {
	(QF.key_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->null
}


fact {
	(QF.size_0) in BSTreeIntVar->i320+BSTreeIntVar->i321+BSTreeIntVar->i322+BSTreeIntVar->i323+BSTreeIntVar->i324+BSTreeIntVar->i325+BSTreeIntVar->i326
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


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 BSTreeIntVar, exactly 6 BSTreeIntVarNode, 1 int, exactly 7 JavaPrimitiveIntegerValue

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




