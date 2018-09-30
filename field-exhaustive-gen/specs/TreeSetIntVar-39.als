module treeset

open Integer7

one sig null {}


one sig TreeSetIntVar {}

abstract sig TreeSetIntVarNode  {}

one sig QF {
    thiz_0:        one TreeSetIntVar, 
    root_0:        TreeSetIntVar -> one (TreeSetIntVarNode+null),
    key_0:         TreeSetIntVarNode -> one (JavaPrimitiveIntegerValue+null),
    blackHeight_0: TreeSetIntVarNode -> one JavaPrimitiveIntegerValue,
    color_0:       TreeSetIntVarNode -> one (boolean),
    fparent_0:      TreeSetIntVarNode -> lone (TreeSetIntVarNode+null),
    bparent_0:      TreeSetIntVarNode -> lone (TreeSetIntVarNode),

    fleft_0:        TreeSetIntVarNode -> lone (TreeSetIntVarNode+null),
    bleft_0:        TreeSetIntVarNode -> lone (TreeSetIntVarNode+null),
    fright_0:       TreeSetIntVarNode -> lone (TreeSetIntVarNode+null),
    bright_0:       TreeSetIntVarNode -> lone (TreeSetIntVarNode+null),
    size_0:        TreeSetIntVar -> one JavaPrimitiveIntegerValue    

}


fact repOk {
   let RED = false,
       BLACK = true,
       key = QF.key_0,
       blackHeight = QF.blackHeight_0,
       left = QF.fleft_0 +QF.bleft_0,
       right = QF.fright_0+QF.bright_0,
       color = QF.color_0,
       parent = QF.fparent_0 + QF.bparent_0,
       root = QF.root_0,
       thiz = QF.thiz_0
   | {

		RED=false &&
		BLACK=true && 
		
        thiz.root.parent in null && 
//		( thiz.root!=null => thiz.root.color = BLACK ) && 
		( all n: TreeSetIntVarNode | n in thiz.root.*(left + right) => (

				/*non_null*/
                                (n.key != null ) &&

				/* parent left */
                                ( n.left != null => n.left.parent = n ) &&

				/* parent right */
				( n.right != null => n.right.parent = n ) &&

				/* parent */
				( n.parent != null => n in n.parent.(left + right) ) &&

				/* form a tree */
				( n !in n.^parent ) &&

				/* left sorted */
				( all x : n.left.^(left + right) + n.left - null | pred_java_primitive_integer_value_gt[n.key,x.key]) &&

				/* right sorted */
				( all x : n.right.^(left + right) + n.right - null | pred_java_primitive_integer_value_gt[x.key,n.key]) &&

				/* no red node has a red parent */
				( n.color = RED && n.parent != null => n.parent.color = BLACK ) &&

				/* black height leaf */
				( ( n.left=null && n.right=null ) => ( equ[n.blackHeight,i321] ) ) &&

				/* black height left non null */
				( n.left!=null && n.right=null => ( 
				      ( n.left.color = RED ) && 
				      ( equ[n.left.blackHeight,i321] ) && 
				      ( equ[n.blackHeight,i321] )  
				)) &&

				/* black height right non null */
				( n.left=null && n.right!=null =>  ( 
				      ( n.right.color = RED ) && 
				      ( equ[n.right.blackHeight,i321] ) && 
				      ( equ[n.blackHeight,i321] ) 
				 )) && 

				/* inner node (RED/RED) */
				( n.left!=null && n.right!=null && n.left.color=RED && n.right.color=RED => ( 
				        ( equ[n.left.blackHeight,n.right.blackHeight] ) && 
				        ( equ[n.blackHeight, n.left.blackHeight] ) 
				)) && 

				/* inner node (BLACK/BLACK) */
				( n.left!=null && n.right!=null && n.left.color=BLACK && n.right.color=BLACK => ( 
				        ( equ[n.left.blackHeight,n.right.blackHeight] ) && 
				        ( equ[n.blackHeight,fun_java_primitive_integer_value_add[n.left.blackHeight,i321]] )  
				)) && 

				/* inner node (RED/BLACK) */
				( n.left!=null && n.right!=null && n.left.color=RED && n.right.color=BLACK => ( 
				        ( equ[n.left.blackHeight,fun_java_primitive_integer_value_add[n.right.blackHeight,i321]] ) && 
				        ( equ[n.blackHeight,n.left.blackHeight]  )  
				)) && 

				/* inner node (BLACK/RED) */
				( n.left!=null && n.right!=null && n.left.color=BLACK && n.right.color=RED => ( 
				        ( equ[n.right.blackHeight,fun_java_primitive_integer_value_add[n.left.blackHeight,i321]] ) && 
				        ( equ[n.blackHeight,n.right.blackHeight]  )   )) 

			)	)

}}



fact {
  all a, b: JavaPrimitiveIntegerValue | 
    (a = b <=> pred_java_primitive_integer_value_eq[a,b]) 
}


fact { 
let entry=(QF.thiz_0).(QF.root_0),ff1=QF.fleft_0,ff2=QF.fright_0,ff3=QF.fparent_0,bf1=QF.bleft_0,bf2=QF.bright_0,bf3=QF.bparent_0 | { 
   -- forwardPlusBackwardAreFunctions 
   no ((ff1.univ) & (bf1.univ)) 
   no ((ff2.univ) & (bf2.univ)) 
   no ((ff3.univ) & (bf3.univ)) 
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38 = ff1.univ + bf1.univ   
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38 = ff2.univ + bf2.univ   
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38 = ff3.univ + bf3.univ   

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



fact notReachableIsFix {all n : TreeSetIntVarNode | n in (TreeSetIntVarNode - (QF.thiz_0).(QF.root_0).*(QF.fleft_0 + QF.fright_0 + QF.fparent_0)) => (
                        no n.(QF.bleft_0) and
                        no n.(QF.bright_0) and
                        no n.(QF.bparent_0) and
                        n.(QF.fleft_0) = null and
                        n.(QF.fright_0) = null and
                        n.(QF.fparent_0) = null and
                        n.(QF.color_0) = false  and
                        n.(QF.blackHeight_0) = i320 and
                        n.(QF.key_0) = i320 
        )
}


fun FReach[] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38) {
    (QF.thiz_0).(QF.root_0).*(QF.fleft_0 + QF.fright_0) - null
}


one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16,N17,N18,N19,N20,N21,N22,N23,N24,N25,N26,N27,N28,N29,N30,N31,N32,N33,N34,N35,N36,N37,N38 extends TreeSetIntVarNode {}


one sig i320,i321,i322,i323,i324,i325,i326,i327,i328,i329,i3210,i3211,i3212,i3213,i3214,i3215,i3216,i3217,i3218,i3219,i3220,i3221,i3222,i3223,i3224,i3225,i3226,i3227,i3228,i3229,i3230,i3231,i3232,i3233,i3234,i3235,i3236,i3237,i3238,i3239 extends JavaPrimitiveIntegerValue {} 
fact {
	// int32 bounds 
	b01 in i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false+i3210->true+i3211->true+i3212->false+i3213->false+i3214->true+i3215->true+i3216->false+i3217->false+i3218->true+i3219->true+i3220->false+i3221->false+i3222->true+i3223->true+i3224->false+i3225->false+i3226->true+i3227->true+i3228->false+i3229->false+i3230->true+i3231->true+i3232->false+i3233->false+i3234->true+i3235->true+i3236->false+i3237->false+i3238->true+i3239->true
	i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false+i3210->true+i3211->true+i3212->false+i3213->false+i3214->true+i3215->true+i3216->false+i3217->false+i3218->true+i3219->true+i3220->false+i3221->false+i3222->true+i3223->true+i3224->false+i3225->false+i3226->true+i3227->true+i3228->false+i3229->false+i3230->true+i3231->true+i3232->false+i3233->false+i3234->true+i3235->true+i3236->false+i3237->false+i3238->true+i3239->true in b01
	b00 in i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true+i3210->false+i3211->true+i3212->false+i3213->true+i3214->false+i3215->true+i3216->false+i3217->true+i3218->false+i3219->true+i3220->false+i3221->true+i3222->false+i3223->true+i3224->false+i3225->true+i3226->false+i3227->true+i3228->false+i3229->true+i3230->false+i3231->true+i3232->false+i3233->true+i3234->false+i3235->true+i3236->false+i3237->true+i3238->false+i3239->true
	i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true+i3210->false+i3211->true+i3212->false+i3213->true+i3214->false+i3215->true+i3216->false+i3217->true+i3218->false+i3219->true+i3220->false+i3221->true+i3222->false+i3223->true+i3224->false+i3225->true+i3226->false+i3227->true+i3228->false+i3229->true+i3230->false+i3231->true+i3232->false+i3233->true+i3234->false+i3235->true+i3236->false+i3237->true+i3238->false+i3239->true in b00
	b05 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false+i3221->false+i3222->false+i3223->false+i3224->false+i3225->false+i3226->false+i3227->false+i3228->false+i3229->false+i3230->false+i3231->false+i3232->true+i3233->true+i3234->true+i3235->true+i3236->true+i3237->true+i3238->true+i3239->true
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false+i3221->false+i3222->false+i3223->false+i3224->false+i3225->false+i3226->false+i3227->false+i3228->false+i3229->false+i3230->false+i3231->false+i3232->true+i3233->true+i3234->true+i3235->true+i3236->true+i3237->true+i3238->true+i3239->true in b05
	b04 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->true+i3217->true+i3218->true+i3219->true+i3220->true+i3221->true+i3222->true+i3223->true+i3224->true+i3225->true+i3226->true+i3227->true+i3228->true+i3229->true+i3230->true+i3231->true+i3232->false+i3233->false+i3234->false+i3235->false+i3236->false+i3237->false+i3238->false+i3239->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->true+i3217->true+i3218->true+i3219->true+i3220->true+i3221->true+i3222->true+i3223->true+i3224->true+i3225->true+i3226->true+i3227->true+i3228->true+i3229->true+i3230->true+i3231->true+i3232->false+i3233->false+i3234->false+i3235->false+i3236->false+i3237->false+i3238->false+i3239->false in b04
	b03 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true+i3210->true+i3211->true+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false+i3221->false+i3222->false+i3223->false+i3224->true+i3225->true+i3226->true+i3227->true+i3228->true+i3229->true+i3230->true+i3231->true+i3232->false+i3233->false+i3234->false+i3235->false+i3236->false+i3237->false+i3238->false+i3239->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true+i3210->true+i3211->true+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false+i3221->false+i3222->false+i3223->false+i3224->true+i3225->true+i3226->true+i3227->true+i3228->true+i3229->true+i3230->true+i3231->true+i3232->false+i3233->false+i3234->false+i3235->false+i3236->false+i3237->false+i3238->false+i3239->false in b03
	b02 in i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false+i3210->false+i3211->false+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->true+i3221->true+i3222->true+i3223->true+i3224->false+i3225->false+i3226->false+i3227->false+i3228->true+i3229->true+i3230->true+i3231->true+i3232->false+i3233->false+i3234->false+i3235->false+i3236->true+i3237->true+i3238->true+i3239->true
	i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false+i3210->false+i3211->false+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->true+i3221->true+i3222->true+i3223->true+i3224->false+i3225->false+i3226->false+i3227->false+i3228->true+i3229->true+i3230->true+i3231->true+i3232->false+i3233->false+i3234->false+i3235->false+i3236->true+i3237->true+i3238->true+i3239->true in b02
	b06 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false+i3221->false+i3222->false+i3223->false+i3224->false+i3225->false+i3226->false+i3227->false+i3228->false+i3229->false+i3230->false+i3231->false+i3232->false+i3233->false+i3234->false+i3235->false+i3236->false+i3237->false+i3238->false+i3239->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false+i3221->false+i3222->false+i3223->false+i3224->false+i3225->false+i3226->false+i3227->false+i3228->false+i3229->false+i3230->false+i3231->false+i3232->false+i3233->false+i3234->false+i3235->false+i3236->false+i3237->false+i3238->false+i3239->false in b06
}



fact { QF.fleft_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->N14+N0->N15+N0->N16+N0->N17+N0->N18+N0->N19+N0->N20+N0->N21+N0->N22+N0->N23+N0->N24+N0->N25+N0->N26+N0->N27+N0->N28+N0->N29+N0->N30+N0->N31+N0->N32+N0->N33+N0->N34+N0->N35+N0->N36+N0->N37+N0->N38+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->N14+N1->N15+N1->N16+N1->N17+N1->N18+N1->N19+N1->N20+N1->N21+N1->N22+N1->N23+N1->N24+N1->N25+N1->N26+N1->N27+N1->N28+N1->N29+N1->N30+N1->N31+N1->N32+N1->N33+N1->N34+N1->N35+N1->N36+N1->N37+N1->N38+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->N14+N2->N15+N2->N16+N2->N17+N2->N18+N2->N19+N2->N20+N2->N21+N2->N22+N2->N23+N2->N24+N2->N25+N2->N26+N2->N27+N2->N28+N2->N29+N2->N30+N2->N31+N2->N32+N2->N33+N2->N34+N2->N35+N2->N36+N2->N37+N2->N38+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->N14+N3->N15+N3->N16+N3->N17+N3->N18+N3->N19+N3->N20+N3->N21+N3->N22+N3->N23+N3->N24+N3->N25+N3->N26+N3->N27+N3->N28+N3->N29+N3->N30+N3->N31+N3->N32+N3->N33+N3->N34+N3->N35+N3->N36+N3->N37+N3->N38+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->N14+N4->N15+N4->N16+N4->N17+N4->N18+N4->N19+N4->N20+N4->N21+N4->N22+N4->N23+N4->N24+N4->N25+N4->N26+N4->N27+N4->N28+N4->N29+N4->N30+N4->N31+N4->N32+N4->N33+N4->N34+N4->N35+N4->N36+N4->N37+N4->N38+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->N14+N5->N15+N5->N16+N5->N17+N5->N18+N5->N19+N5->N20+N5->N21+N5->N22+N5->N23+N5->N24+N5->N25+N5->N26+N5->N27+N5->N28+N5->N29+N5->N30+N5->N31+N5->N32+N5->N33+N5->N34+N5->N35+N5->N36+N5->N37+N5->N38+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->N14+N6->N15+N6->N16+N6->N17+N6->N18+N6->N19+N6->N20+N6->N21+N6->N22+N6->N23+N6->N24+N6->N25+N6->N26+N6->N27+N6->N28+N6->N29+N6->N30+N6->N31+N6->N32+N6->N33+N6->N34+N6->N35+N6->N36+N6->N37+N6->N38+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->N14+N7->N15+N7->N16+N7->N17+N7->N18+N7->N19+N7->N20+N7->N21+N7->N22+N7->N23+N7->N24+N7->N25+N7->N26+N7->N27+N7->N28+N7->N29+N7->N30+N7->N31+N7->N32+N7->N33+N7->N34+N7->N35+N7->N36+N7->N37+N7->N38+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->N14+N8->N15+N8->N16+N8->N17+N8->N18+N8->N19+N8->N20+N8->N21+N8->N22+N8->N23+N8->N24+N8->N25+N8->N26+N8->N27+N8->N28+N8->N29+N8->N30+N8->N31+N8->N32+N8->N33+N8->N34+N8->N35+N8->N36+N8->N37+N8->N38+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->N14+N9->N15+N9->N16+N9->N17+N9->N18+N9->N19+N9->N20+N9->N21+N9->N22+N9->N23+N9->N24+N9->N25+N9->N26+N9->N27+N9->N28+N9->N29+N9->N30+N9->N31+N9->N32+N9->N33+N9->N34+N9->N35+N9->N36+N9->N37+N9->N38+N9->null+N10->N11+N10->N12+N10->N13+N10->N14+N10->N15+N10->N16+N10->N17+N10->N18+N10->N19+N10->N20+N10->N21+N10->N22+N10->N23+N10->N24+N10->N25+N10->N26+N10->N27+N10->N28+N10->N29+N10->N30+N10->N31+N10->N32+N10->N33+N10->N34+N10->N35+N10->N36+N10->N37+N10->N38+N10->null+N11->N12+N11->N13+N11->N14+N11->N15+N11->N16+N11->N17+N11->N18+N11->N19+N11->N20+N11->N21+N11->N22+N11->N23+N11->N24+N11->N25+N11->N26+N11->N27+N11->N28+N11->N29+N11->N30+N11->N31+N11->N32+N11->N33+N11->N34+N11->N35+N11->N36+N11->N37+N11->N38+N11->null+N12->N13+N12->N14+N12->N15+N12->N16+N12->N17+N12->N18+N12->N19+N12->N20+N12->N21+N12->N22+N12->N23+N12->N24+N12->N25+N12->N26+N12->N27+N12->N28+N12->N29+N12->N30+N12->N31+N12->N32+N12->N33+N12->N34+N12->N35+N12->N36+N12->N37+N12->N38+N12->null+N13->N14+N13->N15+N13->N16+N13->N17+N13->N18+N13->N19+N13->N20+N13->N21+N13->N22+N13->N23+N13->N24+N13->N25+N13->N26+N13->N27+N13->N28+N13->N29+N13->N30+N13->N31+N13->N32+N13->N33+N13->N34+N13->N35+N13->N36+N13->N37+N13->N38+N13->null+N14->N15+N14->N16+N14->N17+N14->N18+N14->N19+N14->N20+N14->N21+N14->N22+N14->N23+N14->N24+N14->N25+N14->N26+N14->N27+N14->N28+N14->N29+N14->N30+N14->N31+N14->N32+N14->N33+N14->N34+N14->N35+N14->N36+N14->N37+N14->N38+N14->null+N15->N16+N15->N17+N15->N18+N15->N19+N15->N20+N15->N21+N15->N22+N15->N23+N15->N24+N15->N25+N15->N26+N15->N27+N15->N28+N15->N29+N15->N30+N15->N31+N15->N32+N15->N33+N15->N34+N15->N35+N15->N36+N15->N37+N15->N38+N15->null+N16->N17+N16->N18+N16->N19+N16->N20+N16->N21+N16->N22+N16->N23+N16->N24+N16->N25+N16->N26+N16->N27+N16->N28+N16->N29+N16->N30+N16->N31+N16->N32+N16->N33+N16->N34+N16->N35+N16->N36+N16->N37+N16->N38+N16->null+N17->N18+N17->N19+N17->N20+N17->N21+N17->N22+N17->N23+N17->N24+N17->N25+N17->N26+N17->N27+N17->N28+N17->N29+N17->N30+N17->N31+N17->N32+N17->N33+N17->N34+N17->N35+N17->N36+N17->N37+N17->N38+N17->null+N18->N19+N18->N20+N18->N21+N18->N22+N18->N23+N18->N24+N18->N25+N18->N26+N18->N27+N18->N28+N18->N29+N18->N30+N18->N31+N18->N32+N18->N33+N18->N34+N18->N35+N18->N36+N18->N37+N18->N38+N18->null+N19->N20+N19->N21+N19->N22+N19->N23+N19->N24+N19->N25+N19->N26+N19->N27+N19->N28+N19->N29+N19->N30+N19->N31+N19->N32+N19->N33+N19->N34+N19->N35+N19->N36+N19->N37+N19->N38+N19->null+N20->N21+N20->N22+N20->N23+N20->N24+N20->N25+N20->N26+N20->N27+N20->N28+N20->N29+N20->N30+N20->N31+N20->N32+N20->N33+N20->N34+N20->N35+N20->N36+N20->N37+N20->N38+N20->null+N21->N22+N21->N23+N21->N24+N21->N25+N21->N26+N21->N27+N21->N28+N21->N29+N21->N30+N21->N31+N21->N32+N21->N33+N21->N34+N21->N35+N21->N36+N21->N37+N21->N38+N21->null+N22->N23+N22->N24+N22->N25+N22->N26+N22->N27+N22->N28+N22->N29+N22->N30+N22->N31+N22->N32+N22->N33+N22->N34+N22->N35+N22->N36+N22->N37+N22->N38+N22->null+N23->N24+N23->N25+N23->N26+N23->N27+N23->N28+N23->N29+N23->N30+N23->N31+N23->N32+N23->N33+N23->N34+N23->N35+N23->N36+N23->N37+N23->N38+N23->null+N24->N25+N24->N26+N24->N27+N24->N28+N24->N29+N24->N30+N24->N31+N24->N32+N24->N33+N24->N34+N24->N35+N24->N36+N24->N37+N24->N38+N24->null+N25->N26+N25->N27+N25->N28+N25->N29+N25->N30+N25->N31+N25->N32+N25->N33+N25->N34+N25->N35+N25->N36+N25->N37+N25->N38+N25->null+N26->N27+N26->N28+N26->N29+N26->N30+N26->N31+N26->N32+N26->N33+N26->N34+N26->N35+N26->N36+N26->N37+N26->N38+N26->null+N27->N28+N27->N29+N27->N30+N27->N31+N27->N32+N27->N33+N27->N34+N27->N35+N27->N36+N27->N37+N27->N38+N27->null+N28->N29+N28->N30+N28->N31+N28->N32+N28->N33+N28->N34+N28->N35+N28->N36+N28->N37+N28->N38+N28->null+N29->N30+N29->N31+N29->N32+N29->N33+N29->N34+N29->N35+N29->N36+N29->N37+N29->N38+N29->null+N30->N31+N30->N32+N30->N33+N30->N34+N30->N35+N30->N36+N30->N37+N30->N38+N30->null+N31->N32+N31->N33+N31->N34+N31->N35+N31->N36+N31->N37+N31->N38+N31->null+N32->N33+N32->N34+N32->N35+N32->N36+N32->N37+N32->N38+N32->null+N33->N34+N33->N35+N33->N36+N33->N37+N33->N38+N33->null+N34->N35+N34->N36+N34->N37+N34->N38+N34->null+N35->N36+N35->N37+N35->N38+N35->null+N36->N37+N36->N38+N36->null+N37->N38+N37->null+N38->null }
fact { QF.fright_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->N14+N0->N15+N0->N16+N0->N17+N0->N18+N0->N19+N0->N20+N0->N21+N0->N22+N0->N23+N0->N24+N0->N25+N0->N26+N0->N27+N0->N28+N0->N29+N0->N30+N0->N31+N0->N32+N0->N33+N0->N34+N0->N35+N0->N36+N0->N37+N0->N38+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->N14+N1->N15+N1->N16+N1->N17+N1->N18+N1->N19+N1->N20+N1->N21+N1->N22+N1->N23+N1->N24+N1->N25+N1->N26+N1->N27+N1->N28+N1->N29+N1->N30+N1->N31+N1->N32+N1->N33+N1->N34+N1->N35+N1->N36+N1->N37+N1->N38+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->N14+N2->N15+N2->N16+N2->N17+N2->N18+N2->N19+N2->N20+N2->N21+N2->N22+N2->N23+N2->N24+N2->N25+N2->N26+N2->N27+N2->N28+N2->N29+N2->N30+N2->N31+N2->N32+N2->N33+N2->N34+N2->N35+N2->N36+N2->N37+N2->N38+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->N14+N3->N15+N3->N16+N3->N17+N3->N18+N3->N19+N3->N20+N3->N21+N3->N22+N3->N23+N3->N24+N3->N25+N3->N26+N3->N27+N3->N28+N3->N29+N3->N30+N3->N31+N3->N32+N3->N33+N3->N34+N3->N35+N3->N36+N3->N37+N3->N38+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->N14+N4->N15+N4->N16+N4->N17+N4->N18+N4->N19+N4->N20+N4->N21+N4->N22+N4->N23+N4->N24+N4->N25+N4->N26+N4->N27+N4->N28+N4->N29+N4->N30+N4->N31+N4->N32+N4->N33+N4->N34+N4->N35+N4->N36+N4->N37+N4->N38+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->N14+N5->N15+N5->N16+N5->N17+N5->N18+N5->N19+N5->N20+N5->N21+N5->N22+N5->N23+N5->N24+N5->N25+N5->N26+N5->N27+N5->N28+N5->N29+N5->N30+N5->N31+N5->N32+N5->N33+N5->N34+N5->N35+N5->N36+N5->N37+N5->N38+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->N14+N6->N15+N6->N16+N6->N17+N6->N18+N6->N19+N6->N20+N6->N21+N6->N22+N6->N23+N6->N24+N6->N25+N6->N26+N6->N27+N6->N28+N6->N29+N6->N30+N6->N31+N6->N32+N6->N33+N6->N34+N6->N35+N6->N36+N6->N37+N6->N38+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->N14+N7->N15+N7->N16+N7->N17+N7->N18+N7->N19+N7->N20+N7->N21+N7->N22+N7->N23+N7->N24+N7->N25+N7->N26+N7->N27+N7->N28+N7->N29+N7->N30+N7->N31+N7->N32+N7->N33+N7->N34+N7->N35+N7->N36+N7->N37+N7->N38+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->N14+N8->N15+N8->N16+N8->N17+N8->N18+N8->N19+N8->N20+N8->N21+N8->N22+N8->N23+N8->N24+N8->N25+N8->N26+N8->N27+N8->N28+N8->N29+N8->N30+N8->N31+N8->N32+N8->N33+N8->N34+N8->N35+N8->N36+N8->N37+N8->N38+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->N14+N9->N15+N9->N16+N9->N17+N9->N18+N9->N19+N9->N20+N9->N21+N9->N22+N9->N23+N9->N24+N9->N25+N9->N26+N9->N27+N9->N28+N9->N29+N9->N30+N9->N31+N9->N32+N9->N33+N9->N34+N9->N35+N9->N36+N9->N37+N9->N38+N9->null+N10->N11+N10->N12+N10->N13+N10->N14+N10->N15+N10->N16+N10->N17+N10->N18+N10->N19+N10->N20+N10->N21+N10->N22+N10->N23+N10->N24+N10->N25+N10->N26+N10->N27+N10->N28+N10->N29+N10->N30+N10->N31+N10->N32+N10->N33+N10->N34+N10->N35+N10->N36+N10->N37+N10->N38+N10->null+N11->N12+N11->N13+N11->N14+N11->N15+N11->N16+N11->N17+N11->N18+N11->N19+N11->N20+N11->N21+N11->N22+N11->N23+N11->N24+N11->N25+N11->N26+N11->N27+N11->N28+N11->N29+N11->N30+N11->N31+N11->N32+N11->N33+N11->N34+N11->N35+N11->N36+N11->N37+N11->N38+N11->null+N12->N13+N12->N14+N12->N15+N12->N16+N12->N17+N12->N18+N12->N19+N12->N20+N12->N21+N12->N22+N12->N23+N12->N24+N12->N25+N12->N26+N12->N27+N12->N28+N12->N29+N12->N30+N12->N31+N12->N32+N12->N33+N12->N34+N12->N35+N12->N36+N12->N37+N12->N38+N12->null+N13->N14+N13->N15+N13->N16+N13->N17+N13->N18+N13->N19+N13->N20+N13->N21+N13->N22+N13->N23+N13->N24+N13->N25+N13->N26+N13->N27+N13->N28+N13->N29+N13->N30+N13->N31+N13->N32+N13->N33+N13->N34+N13->N35+N13->N36+N13->N37+N13->N38+N13->null+N14->N15+N14->N16+N14->N17+N14->N18+N14->N19+N14->N20+N14->N21+N14->N22+N14->N23+N14->N24+N14->N25+N14->N26+N14->N27+N14->N28+N14->N29+N14->N30+N14->N31+N14->N32+N14->N33+N14->N34+N14->N35+N14->N36+N14->N37+N14->N38+N14->null+N15->N16+N15->N17+N15->N18+N15->N19+N15->N20+N15->N21+N15->N22+N15->N23+N15->N24+N15->N25+N15->N26+N15->N27+N15->N28+N15->N29+N15->N30+N15->N31+N15->N32+N15->N33+N15->N34+N15->N35+N15->N36+N15->N37+N15->N38+N15->null+N16->N17+N16->N18+N16->N19+N16->N20+N16->N21+N16->N22+N16->N23+N16->N24+N16->N25+N16->N26+N16->N27+N16->N28+N16->N29+N16->N30+N16->N31+N16->N32+N16->N33+N16->N34+N16->N35+N16->N36+N16->N37+N16->N38+N16->null+N17->N18+N17->N19+N17->N20+N17->N21+N17->N22+N17->N23+N17->N24+N17->N25+N17->N26+N17->N27+N17->N28+N17->N29+N17->N30+N17->N31+N17->N32+N17->N33+N17->N34+N17->N35+N17->N36+N17->N37+N17->N38+N17->null+N18->N19+N18->N20+N18->N21+N18->N22+N18->N23+N18->N24+N18->N25+N18->N26+N18->N27+N18->N28+N18->N29+N18->N30+N18->N31+N18->N32+N18->N33+N18->N34+N18->N35+N18->N36+N18->N37+N18->N38+N18->null+N19->N20+N19->N21+N19->N22+N19->N23+N19->N24+N19->N25+N19->N26+N19->N27+N19->N28+N19->N29+N19->N30+N19->N31+N19->N32+N19->N33+N19->N34+N19->N35+N19->N36+N19->N37+N19->N38+N19->null+N20->N21+N20->N22+N20->N23+N20->N24+N20->N25+N20->N26+N20->N27+N20->N28+N20->N29+N20->N30+N20->N31+N20->N32+N20->N33+N20->N34+N20->N35+N20->N36+N20->N37+N20->N38+N20->null+N21->N22+N21->N23+N21->N24+N21->N25+N21->N26+N21->N27+N21->N28+N21->N29+N21->N30+N21->N31+N21->N32+N21->N33+N21->N34+N21->N35+N21->N36+N21->N37+N21->N38+N21->null+N22->N23+N22->N24+N22->N25+N22->N26+N22->N27+N22->N28+N22->N29+N22->N30+N22->N31+N22->N32+N22->N33+N22->N34+N22->N35+N22->N36+N22->N37+N22->N38+N22->null+N23->N24+N23->N25+N23->N26+N23->N27+N23->N28+N23->N29+N23->N30+N23->N31+N23->N32+N23->N33+N23->N34+N23->N35+N23->N36+N23->N37+N23->N38+N23->null+N24->N25+N24->N26+N24->N27+N24->N28+N24->N29+N24->N30+N24->N31+N24->N32+N24->N33+N24->N34+N24->N35+N24->N36+N24->N37+N24->N38+N24->null+N25->N26+N25->N27+N25->N28+N25->N29+N25->N30+N25->N31+N25->N32+N25->N33+N25->N34+N25->N35+N25->N36+N25->N37+N25->N38+N25->null+N26->N27+N26->N28+N26->N29+N26->N30+N26->N31+N26->N32+N26->N33+N26->N34+N26->N35+N26->N36+N26->N37+N26->N38+N26->null+N27->N28+N27->N29+N27->N30+N27->N31+N27->N32+N27->N33+N27->N34+N27->N35+N27->N36+N27->N37+N27->N38+N27->null+N28->N29+N28->N30+N28->N31+N28->N32+N28->N33+N28->N34+N28->N35+N28->N36+N28->N37+N28->N38+N28->null+N29->N30+N29->N31+N29->N32+N29->N33+N29->N34+N29->N35+N29->N36+N29->N37+N29->N38+N29->null+N30->N31+N30->N32+N30->N33+N30->N34+N30->N35+N30->N36+N30->N37+N30->N38+N30->null+N31->N32+N31->N33+N31->N34+N31->N35+N31->N36+N31->N37+N31->N38+N31->null+N32->N33+N32->N34+N32->N35+N32->N36+N32->N37+N32->N38+N32->null+N33->N34+N33->N35+N33->N36+N33->N37+N33->N38+N33->null+N34->N35+N34->N36+N34->N37+N34->N38+N34->null+N35->N36+N35->N37+N35->N38+N35->null+N36->N37+N36->N38+N36->null+N37->N38+N37->null+N38->null }
fact { QF.fparent_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->N14+N0->N15+N0->N16+N0->N17+N0->N18+N0->N19+N0->N20+N0->N21+N0->N22+N0->N23+N0->N24+N0->N25+N0->N26+N0->N27+N0->N28+N0->N29+N0->N30+N0->N31+N0->N32+N0->N33+N0->N34+N0->N35+N0->N36+N0->N37+N0->N38+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->N14+N1->N15+N1->N16+N1->N17+N1->N18+N1->N19+N1->N20+N1->N21+N1->N22+N1->N23+N1->N24+N1->N25+N1->N26+N1->N27+N1->N28+N1->N29+N1->N30+N1->N31+N1->N32+N1->N33+N1->N34+N1->N35+N1->N36+N1->N37+N1->N38+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->N14+N2->N15+N2->N16+N2->N17+N2->N18+N2->N19+N2->N20+N2->N21+N2->N22+N2->N23+N2->N24+N2->N25+N2->N26+N2->N27+N2->N28+N2->N29+N2->N30+N2->N31+N2->N32+N2->N33+N2->N34+N2->N35+N2->N36+N2->N37+N2->N38+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->N14+N3->N15+N3->N16+N3->N17+N3->N18+N3->N19+N3->N20+N3->N21+N3->N22+N3->N23+N3->N24+N3->N25+N3->N26+N3->N27+N3->N28+N3->N29+N3->N30+N3->N31+N3->N32+N3->N33+N3->N34+N3->N35+N3->N36+N3->N37+N3->N38+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->N14+N4->N15+N4->N16+N4->N17+N4->N18+N4->N19+N4->N20+N4->N21+N4->N22+N4->N23+N4->N24+N4->N25+N4->N26+N4->N27+N4->N28+N4->N29+N4->N30+N4->N31+N4->N32+N4->N33+N4->N34+N4->N35+N4->N36+N4->N37+N4->N38+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->N14+N5->N15+N5->N16+N5->N17+N5->N18+N5->N19+N5->N20+N5->N21+N5->N22+N5->N23+N5->N24+N5->N25+N5->N26+N5->N27+N5->N28+N5->N29+N5->N30+N5->N31+N5->N32+N5->N33+N5->N34+N5->N35+N5->N36+N5->N37+N5->N38+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->N14+N6->N15+N6->N16+N6->N17+N6->N18+N6->N19+N6->N20+N6->N21+N6->N22+N6->N23+N6->N24+N6->N25+N6->N26+N6->N27+N6->N28+N6->N29+N6->N30+N6->N31+N6->N32+N6->N33+N6->N34+N6->N35+N6->N36+N6->N37+N6->N38+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->N14+N7->N15+N7->N16+N7->N17+N7->N18+N7->N19+N7->N20+N7->N21+N7->N22+N7->N23+N7->N24+N7->N25+N7->N26+N7->N27+N7->N28+N7->N29+N7->N30+N7->N31+N7->N32+N7->N33+N7->N34+N7->N35+N7->N36+N7->N37+N7->N38+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->N14+N8->N15+N8->N16+N8->N17+N8->N18+N8->N19+N8->N20+N8->N21+N8->N22+N8->N23+N8->N24+N8->N25+N8->N26+N8->N27+N8->N28+N8->N29+N8->N30+N8->N31+N8->N32+N8->N33+N8->N34+N8->N35+N8->N36+N8->N37+N8->N38+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->N14+N9->N15+N9->N16+N9->N17+N9->N18+N9->N19+N9->N20+N9->N21+N9->N22+N9->N23+N9->N24+N9->N25+N9->N26+N9->N27+N9->N28+N9->N29+N9->N30+N9->N31+N9->N32+N9->N33+N9->N34+N9->N35+N9->N36+N9->N37+N9->N38+N9->null+N10->N11+N10->N12+N10->N13+N10->N14+N10->N15+N10->N16+N10->N17+N10->N18+N10->N19+N10->N20+N10->N21+N10->N22+N10->N23+N10->N24+N10->N25+N10->N26+N10->N27+N10->N28+N10->N29+N10->N30+N10->N31+N10->N32+N10->N33+N10->N34+N10->N35+N10->N36+N10->N37+N10->N38+N10->null+N11->N12+N11->N13+N11->N14+N11->N15+N11->N16+N11->N17+N11->N18+N11->N19+N11->N20+N11->N21+N11->N22+N11->N23+N11->N24+N11->N25+N11->N26+N11->N27+N11->N28+N11->N29+N11->N30+N11->N31+N11->N32+N11->N33+N11->N34+N11->N35+N11->N36+N11->N37+N11->N38+N11->null+N12->N13+N12->N14+N12->N15+N12->N16+N12->N17+N12->N18+N12->N19+N12->N20+N12->N21+N12->N22+N12->N23+N12->N24+N12->N25+N12->N26+N12->N27+N12->N28+N12->N29+N12->N30+N12->N31+N12->N32+N12->N33+N12->N34+N12->N35+N12->N36+N12->N37+N12->N38+N12->null+N13->N14+N13->N15+N13->N16+N13->N17+N13->N18+N13->N19+N13->N20+N13->N21+N13->N22+N13->N23+N13->N24+N13->N25+N13->N26+N13->N27+N13->N28+N13->N29+N13->N30+N13->N31+N13->N32+N13->N33+N13->N34+N13->N35+N13->N36+N13->N37+N13->N38+N13->null+N14->N15+N14->N16+N14->N17+N14->N18+N14->N19+N14->N20+N14->N21+N14->N22+N14->N23+N14->N24+N14->N25+N14->N26+N14->N27+N14->N28+N14->N29+N14->N30+N14->N31+N14->N32+N14->N33+N14->N34+N14->N35+N14->N36+N14->N37+N14->N38+N14->null+N15->N16+N15->N17+N15->N18+N15->N19+N15->N20+N15->N21+N15->N22+N15->N23+N15->N24+N15->N25+N15->N26+N15->N27+N15->N28+N15->N29+N15->N30+N15->N31+N15->N32+N15->N33+N15->N34+N15->N35+N15->N36+N15->N37+N15->N38+N15->null+N16->N17+N16->N18+N16->N19+N16->N20+N16->N21+N16->N22+N16->N23+N16->N24+N16->N25+N16->N26+N16->N27+N16->N28+N16->N29+N16->N30+N16->N31+N16->N32+N16->N33+N16->N34+N16->N35+N16->N36+N16->N37+N16->N38+N16->null+N17->N18+N17->N19+N17->N20+N17->N21+N17->N22+N17->N23+N17->N24+N17->N25+N17->N26+N17->N27+N17->N28+N17->N29+N17->N30+N17->N31+N17->N32+N17->N33+N17->N34+N17->N35+N17->N36+N17->N37+N17->N38+N17->null+N18->N19+N18->N20+N18->N21+N18->N22+N18->N23+N18->N24+N18->N25+N18->N26+N18->N27+N18->N28+N18->N29+N18->N30+N18->N31+N18->N32+N18->N33+N18->N34+N18->N35+N18->N36+N18->N37+N18->N38+N18->null+N19->N20+N19->N21+N19->N22+N19->N23+N19->N24+N19->N25+N19->N26+N19->N27+N19->N28+N19->N29+N19->N30+N19->N31+N19->N32+N19->N33+N19->N34+N19->N35+N19->N36+N19->N37+N19->N38+N19->null+N20->N21+N20->N22+N20->N23+N20->N24+N20->N25+N20->N26+N20->N27+N20->N28+N20->N29+N20->N30+N20->N31+N20->N32+N20->N33+N20->N34+N20->N35+N20->N36+N20->N37+N20->N38+N20->null+N21->N22+N21->N23+N21->N24+N21->N25+N21->N26+N21->N27+N21->N28+N21->N29+N21->N30+N21->N31+N21->N32+N21->N33+N21->N34+N21->N35+N21->N36+N21->N37+N21->N38+N21->null+N22->N23+N22->N24+N22->N25+N22->N26+N22->N27+N22->N28+N22->N29+N22->N30+N22->N31+N22->N32+N22->N33+N22->N34+N22->N35+N22->N36+N22->N37+N22->N38+N22->null+N23->N24+N23->N25+N23->N26+N23->N27+N23->N28+N23->N29+N23->N30+N23->N31+N23->N32+N23->N33+N23->N34+N23->N35+N23->N36+N23->N37+N23->N38+N23->null+N24->N25+N24->N26+N24->N27+N24->N28+N24->N29+N24->N30+N24->N31+N24->N32+N24->N33+N24->N34+N24->N35+N24->N36+N24->N37+N24->N38+N24->null+N25->N26+N25->N27+N25->N28+N25->N29+N25->N30+N25->N31+N25->N32+N25->N33+N25->N34+N25->N35+N25->N36+N25->N37+N25->N38+N25->null+N26->N27+N26->N28+N26->N29+N26->N30+N26->N31+N26->N32+N26->N33+N26->N34+N26->N35+N26->N36+N26->N37+N26->N38+N26->null+N27->N28+N27->N29+N27->N30+N27->N31+N27->N32+N27->N33+N27->N34+N27->N35+N27->N36+N27->N37+N27->N38+N27->null+N28->N29+N28->N30+N28->N31+N28->N32+N28->N33+N28->N34+N28->N35+N28->N36+N28->N37+N28->N38+N28->null+N29->N30+N29->N31+N29->N32+N29->N33+N29->N34+N29->N35+N29->N36+N29->N37+N29->N38+N29->null+N30->N31+N30->N32+N30->N33+N30->N34+N30->N35+N30->N36+N30->N37+N30->N38+N30->null+N31->N32+N31->N33+N31->N34+N31->N35+N31->N36+N31->N37+N31->N38+N31->null+N32->N33+N32->N34+N32->N35+N32->N36+N32->N37+N32->N38+N32->null+N33->N34+N33->N35+N33->N36+N33->N37+N33->N38+N33->null+N34->N35+N34->N36+N34->N37+N34->N38+N34->null+N35->N36+N35->N37+N35->N38+N35->null+N36->N37+N36->N38+N36->null+N37->N38+N37->null+N38->null }
fact { QF.bleft_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13+N14->N0+N14->N1+N14->N2+N14->N3+N14->N4+N14->N5+N14->N6+N14->N7+N14->N8+N14->N9+N14->N10+N14->N11+N14->N12+N14->N13+N14->N14+N15->N0+N15->N1+N15->N2+N15->N3+N15->N4+N15->N5+N15->N6+N15->N7+N15->N8+N15->N9+N15->N10+N15->N11+N15->N12+N15->N13+N15->N14+N15->N15+N16->N0+N16->N1+N16->N2+N16->N3+N16->N4+N16->N5+N16->N6+N16->N7+N16->N8+N16->N9+N16->N10+N16->N11+N16->N12+N16->N13+N16->N14+N16->N15+N16->N16+N17->N0+N17->N1+N17->N2+N17->N3+N17->N4+N17->N5+N17->N6+N17->N7+N17->N8+N17->N9+N17->N10+N17->N11+N17->N12+N17->N13+N17->N14+N17->N15+N17->N16+N17->N17+N18->N0+N18->N1+N18->N2+N18->N3+N18->N4+N18->N5+N18->N6+N18->N7+N18->N8+N18->N9+N18->N10+N18->N11+N18->N12+N18->N13+N18->N14+N18->N15+N18->N16+N18->N17+N18->N18+N19->N0+N19->N1+N19->N2+N19->N3+N19->N4+N19->N5+N19->N6+N19->N7+N19->N8+N19->N9+N19->N10+N19->N11+N19->N12+N19->N13+N19->N14+N19->N15+N19->N16+N19->N17+N19->N18+N19->N19+N20->N0+N20->N1+N20->N2+N20->N3+N20->N4+N20->N5+N20->N6+N20->N7+N20->N8+N20->N9+N20->N10+N20->N11+N20->N12+N20->N13+N20->N14+N20->N15+N20->N16+N20->N17+N20->N18+N20->N19+N20->N20+N21->N0+N21->N1+N21->N2+N21->N3+N21->N4+N21->N5+N21->N6+N21->N7+N21->N8+N21->N9+N21->N10+N21->N11+N21->N12+N21->N13+N21->N14+N21->N15+N21->N16+N21->N17+N21->N18+N21->N19+N21->N20+N21->N21+N22->N0+N22->N1+N22->N2+N22->N3+N22->N4+N22->N5+N22->N6+N22->N7+N22->N8+N22->N9+N22->N10+N22->N11+N22->N12+N22->N13+N22->N14+N22->N15+N22->N16+N22->N17+N22->N18+N22->N19+N22->N20+N22->N21+N22->N22+N23->N0+N23->N1+N23->N2+N23->N3+N23->N4+N23->N5+N23->N6+N23->N7+N23->N8+N23->N9+N23->N10+N23->N11+N23->N12+N23->N13+N23->N14+N23->N15+N23->N16+N23->N17+N23->N18+N23->N19+N23->N20+N23->N21+N23->N22+N23->N23+N24->N0+N24->N1+N24->N2+N24->N3+N24->N4+N24->N5+N24->N6+N24->N7+N24->N8+N24->N9+N24->N10+N24->N11+N24->N12+N24->N13+N24->N14+N24->N15+N24->N16+N24->N17+N24->N18+N24->N19+N24->N20+N24->N21+N24->N22+N24->N23+N24->N24+N25->N0+N25->N1+N25->N2+N25->N3+N25->N4+N25->N5+N25->N6+N25->N7+N25->N8+N25->N9+N25->N10+N25->N11+N25->N12+N25->N13+N25->N14+N25->N15+N25->N16+N25->N17+N25->N18+N25->N19+N25->N20+N25->N21+N25->N22+N25->N23+N25->N24+N25->N25+N26->N0+N26->N1+N26->N2+N26->N3+N26->N4+N26->N5+N26->N6+N26->N7+N26->N8+N26->N9+N26->N10+N26->N11+N26->N12+N26->N13+N26->N14+N26->N15+N26->N16+N26->N17+N26->N18+N26->N19+N26->N20+N26->N21+N26->N22+N26->N23+N26->N24+N26->N25+N26->N26+N27->N0+N27->N1+N27->N2+N27->N3+N27->N4+N27->N5+N27->N6+N27->N7+N27->N8+N27->N9+N27->N10+N27->N11+N27->N12+N27->N13+N27->N14+N27->N15+N27->N16+N27->N17+N27->N18+N27->N19+N27->N20+N27->N21+N27->N22+N27->N23+N27->N24+N27->N25+N27->N26+N27->N27+N28->N0+N28->N1+N28->N2+N28->N3+N28->N4+N28->N5+N28->N6+N28->N7+N28->N8+N28->N9+N28->N10+N28->N11+N28->N12+N28->N13+N28->N14+N28->N15+N28->N16+N28->N17+N28->N18+N28->N19+N28->N20+N28->N21+N28->N22+N28->N23+N28->N24+N28->N25+N28->N26+N28->N27+N28->N28+N29->N0+N29->N1+N29->N2+N29->N3+N29->N4+N29->N5+N29->N6+N29->N7+N29->N8+N29->N9+N29->N10+N29->N11+N29->N12+N29->N13+N29->N14+N29->N15+N29->N16+N29->N17+N29->N18+N29->N19+N29->N20+N29->N21+N29->N22+N29->N23+N29->N24+N29->N25+N29->N26+N29->N27+N29->N28+N29->N29+N30->N0+N30->N1+N30->N2+N30->N3+N30->N4+N30->N5+N30->N6+N30->N7+N30->N8+N30->N9+N30->N10+N30->N11+N30->N12+N30->N13+N30->N14+N30->N15+N30->N16+N30->N17+N30->N18+N30->N19+N30->N20+N30->N21+N30->N22+N30->N23+N30->N24+N30->N25+N30->N26+N30->N27+N30->N28+N30->N29+N30->N30+N31->N0+N31->N1+N31->N2+N31->N3+N31->N4+N31->N5+N31->N6+N31->N7+N31->N8+N31->N9+N31->N10+N31->N11+N31->N12+N31->N13+N31->N14+N31->N15+N31->N16+N31->N17+N31->N18+N31->N19+N31->N20+N31->N21+N31->N22+N31->N23+N31->N24+N31->N25+N31->N26+N31->N27+N31->N28+N31->N29+N31->N30+N31->N31+N32->N0+N32->N1+N32->N2+N32->N3+N32->N4+N32->N5+N32->N6+N32->N7+N32->N8+N32->N9+N32->N10+N32->N11+N32->N12+N32->N13+N32->N14+N32->N15+N32->N16+N32->N17+N32->N18+N32->N19+N32->N20+N32->N21+N32->N22+N32->N23+N32->N24+N32->N25+N32->N26+N32->N27+N32->N28+N32->N29+N32->N30+N32->N31+N32->N32+N33->N0+N33->N1+N33->N2+N33->N3+N33->N4+N33->N5+N33->N6+N33->N7+N33->N8+N33->N9+N33->N10+N33->N11+N33->N12+N33->N13+N33->N14+N33->N15+N33->N16+N33->N17+N33->N18+N33->N19+N33->N20+N33->N21+N33->N22+N33->N23+N33->N24+N33->N25+N33->N26+N33->N27+N33->N28+N33->N29+N33->N30+N33->N31+N33->N32+N33->N33+N34->N0+N34->N1+N34->N2+N34->N3+N34->N4+N34->N5+N34->N6+N34->N7+N34->N8+N34->N9+N34->N10+N34->N11+N34->N12+N34->N13+N34->N14+N34->N15+N34->N16+N34->N17+N34->N18+N34->N19+N34->N20+N34->N21+N34->N22+N34->N23+N34->N24+N34->N25+N34->N26+N34->N27+N34->N28+N34->N29+N34->N30+N34->N31+N34->N32+N34->N33+N34->N34+N35->N0+N35->N1+N35->N2+N35->N3+N35->N4+N35->N5+N35->N6+N35->N7+N35->N8+N35->N9+N35->N10+N35->N11+N35->N12+N35->N13+N35->N14+N35->N15+N35->N16+N35->N17+N35->N18+N35->N19+N35->N20+N35->N21+N35->N22+N35->N23+N35->N24+N35->N25+N35->N26+N35->N27+N35->N28+N35->N29+N35->N30+N35->N31+N35->N32+N35->N33+N35->N34+N35->N35+N36->N0+N36->N1+N36->N2+N36->N3+N36->N4+N36->N5+N36->N6+N36->N7+N36->N8+N36->N9+N36->N10+N36->N11+N36->N12+N36->N13+N36->N14+N36->N15+N36->N16+N36->N17+N36->N18+N36->N19+N36->N20+N36->N21+N36->N22+N36->N23+N36->N24+N36->N25+N36->N26+N36->N27+N36->N28+N36->N29+N36->N30+N36->N31+N36->N32+N36->N33+N36->N34+N36->N35+N36->N36+N37->N0+N37->N1+N37->N2+N37->N3+N37->N4+N37->N5+N37->N6+N37->N7+N37->N8+N37->N9+N37->N10+N37->N11+N37->N12+N37->N13+N37->N14+N37->N15+N37->N16+N37->N17+N37->N18+N37->N19+N37->N20+N37->N21+N37->N22+N37->N23+N37->N24+N37->N25+N37->N26+N37->N27+N37->N28+N37->N29+N37->N30+N37->N31+N37->N32+N37->N33+N37->N34+N37->N35+N37->N36+N37->N37+N38->N0+N38->N1+N38->N2+N38->N3+N38->N4+N38->N5+N38->N6+N38->N7+N38->N8+N38->N9+N38->N10+N38->N11+N38->N12+N38->N13+N38->N14+N38->N15+N38->N16+N38->N17+N38->N18+N38->N19+N38->N20+N38->N21+N38->N22+N38->N23+N38->N24+N38->N25+N38->N26+N38->N27+N38->N28+N38->N29+N38->N30+N38->N31+N38->N32+N38->N33+N38->N34+N38->N35+N38->N36+N38->N37+N38->N38 }
fact { QF.bright_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13+N14->N0+N14->N1+N14->N2+N14->N3+N14->N4+N14->N5+N14->N6+N14->N7+N14->N8+N14->N9+N14->N10+N14->N11+N14->N12+N14->N13+N14->N14+N15->N0+N15->N1+N15->N2+N15->N3+N15->N4+N15->N5+N15->N6+N15->N7+N15->N8+N15->N9+N15->N10+N15->N11+N15->N12+N15->N13+N15->N14+N15->N15+N16->N0+N16->N1+N16->N2+N16->N3+N16->N4+N16->N5+N16->N6+N16->N7+N16->N8+N16->N9+N16->N10+N16->N11+N16->N12+N16->N13+N16->N14+N16->N15+N16->N16+N17->N0+N17->N1+N17->N2+N17->N3+N17->N4+N17->N5+N17->N6+N17->N7+N17->N8+N17->N9+N17->N10+N17->N11+N17->N12+N17->N13+N17->N14+N17->N15+N17->N16+N17->N17+N18->N0+N18->N1+N18->N2+N18->N3+N18->N4+N18->N5+N18->N6+N18->N7+N18->N8+N18->N9+N18->N10+N18->N11+N18->N12+N18->N13+N18->N14+N18->N15+N18->N16+N18->N17+N18->N18+N19->N0+N19->N1+N19->N2+N19->N3+N19->N4+N19->N5+N19->N6+N19->N7+N19->N8+N19->N9+N19->N10+N19->N11+N19->N12+N19->N13+N19->N14+N19->N15+N19->N16+N19->N17+N19->N18+N19->N19+N20->N0+N20->N1+N20->N2+N20->N3+N20->N4+N20->N5+N20->N6+N20->N7+N20->N8+N20->N9+N20->N10+N20->N11+N20->N12+N20->N13+N20->N14+N20->N15+N20->N16+N20->N17+N20->N18+N20->N19+N20->N20+N21->N0+N21->N1+N21->N2+N21->N3+N21->N4+N21->N5+N21->N6+N21->N7+N21->N8+N21->N9+N21->N10+N21->N11+N21->N12+N21->N13+N21->N14+N21->N15+N21->N16+N21->N17+N21->N18+N21->N19+N21->N20+N21->N21+N22->N0+N22->N1+N22->N2+N22->N3+N22->N4+N22->N5+N22->N6+N22->N7+N22->N8+N22->N9+N22->N10+N22->N11+N22->N12+N22->N13+N22->N14+N22->N15+N22->N16+N22->N17+N22->N18+N22->N19+N22->N20+N22->N21+N22->N22+N23->N0+N23->N1+N23->N2+N23->N3+N23->N4+N23->N5+N23->N6+N23->N7+N23->N8+N23->N9+N23->N10+N23->N11+N23->N12+N23->N13+N23->N14+N23->N15+N23->N16+N23->N17+N23->N18+N23->N19+N23->N20+N23->N21+N23->N22+N23->N23+N24->N0+N24->N1+N24->N2+N24->N3+N24->N4+N24->N5+N24->N6+N24->N7+N24->N8+N24->N9+N24->N10+N24->N11+N24->N12+N24->N13+N24->N14+N24->N15+N24->N16+N24->N17+N24->N18+N24->N19+N24->N20+N24->N21+N24->N22+N24->N23+N24->N24+N25->N0+N25->N1+N25->N2+N25->N3+N25->N4+N25->N5+N25->N6+N25->N7+N25->N8+N25->N9+N25->N10+N25->N11+N25->N12+N25->N13+N25->N14+N25->N15+N25->N16+N25->N17+N25->N18+N25->N19+N25->N20+N25->N21+N25->N22+N25->N23+N25->N24+N25->N25+N26->N0+N26->N1+N26->N2+N26->N3+N26->N4+N26->N5+N26->N6+N26->N7+N26->N8+N26->N9+N26->N10+N26->N11+N26->N12+N26->N13+N26->N14+N26->N15+N26->N16+N26->N17+N26->N18+N26->N19+N26->N20+N26->N21+N26->N22+N26->N23+N26->N24+N26->N25+N26->N26+N27->N0+N27->N1+N27->N2+N27->N3+N27->N4+N27->N5+N27->N6+N27->N7+N27->N8+N27->N9+N27->N10+N27->N11+N27->N12+N27->N13+N27->N14+N27->N15+N27->N16+N27->N17+N27->N18+N27->N19+N27->N20+N27->N21+N27->N22+N27->N23+N27->N24+N27->N25+N27->N26+N27->N27+N28->N0+N28->N1+N28->N2+N28->N3+N28->N4+N28->N5+N28->N6+N28->N7+N28->N8+N28->N9+N28->N10+N28->N11+N28->N12+N28->N13+N28->N14+N28->N15+N28->N16+N28->N17+N28->N18+N28->N19+N28->N20+N28->N21+N28->N22+N28->N23+N28->N24+N28->N25+N28->N26+N28->N27+N28->N28+N29->N0+N29->N1+N29->N2+N29->N3+N29->N4+N29->N5+N29->N6+N29->N7+N29->N8+N29->N9+N29->N10+N29->N11+N29->N12+N29->N13+N29->N14+N29->N15+N29->N16+N29->N17+N29->N18+N29->N19+N29->N20+N29->N21+N29->N22+N29->N23+N29->N24+N29->N25+N29->N26+N29->N27+N29->N28+N29->N29+N30->N0+N30->N1+N30->N2+N30->N3+N30->N4+N30->N5+N30->N6+N30->N7+N30->N8+N30->N9+N30->N10+N30->N11+N30->N12+N30->N13+N30->N14+N30->N15+N30->N16+N30->N17+N30->N18+N30->N19+N30->N20+N30->N21+N30->N22+N30->N23+N30->N24+N30->N25+N30->N26+N30->N27+N30->N28+N30->N29+N30->N30+N31->N0+N31->N1+N31->N2+N31->N3+N31->N4+N31->N5+N31->N6+N31->N7+N31->N8+N31->N9+N31->N10+N31->N11+N31->N12+N31->N13+N31->N14+N31->N15+N31->N16+N31->N17+N31->N18+N31->N19+N31->N20+N31->N21+N31->N22+N31->N23+N31->N24+N31->N25+N31->N26+N31->N27+N31->N28+N31->N29+N31->N30+N31->N31+N32->N0+N32->N1+N32->N2+N32->N3+N32->N4+N32->N5+N32->N6+N32->N7+N32->N8+N32->N9+N32->N10+N32->N11+N32->N12+N32->N13+N32->N14+N32->N15+N32->N16+N32->N17+N32->N18+N32->N19+N32->N20+N32->N21+N32->N22+N32->N23+N32->N24+N32->N25+N32->N26+N32->N27+N32->N28+N32->N29+N32->N30+N32->N31+N32->N32+N33->N0+N33->N1+N33->N2+N33->N3+N33->N4+N33->N5+N33->N6+N33->N7+N33->N8+N33->N9+N33->N10+N33->N11+N33->N12+N33->N13+N33->N14+N33->N15+N33->N16+N33->N17+N33->N18+N33->N19+N33->N20+N33->N21+N33->N22+N33->N23+N33->N24+N33->N25+N33->N26+N33->N27+N33->N28+N33->N29+N33->N30+N33->N31+N33->N32+N33->N33+N34->N0+N34->N1+N34->N2+N34->N3+N34->N4+N34->N5+N34->N6+N34->N7+N34->N8+N34->N9+N34->N10+N34->N11+N34->N12+N34->N13+N34->N14+N34->N15+N34->N16+N34->N17+N34->N18+N34->N19+N34->N20+N34->N21+N34->N22+N34->N23+N34->N24+N34->N25+N34->N26+N34->N27+N34->N28+N34->N29+N34->N30+N34->N31+N34->N32+N34->N33+N34->N34+N35->N0+N35->N1+N35->N2+N35->N3+N35->N4+N35->N5+N35->N6+N35->N7+N35->N8+N35->N9+N35->N10+N35->N11+N35->N12+N35->N13+N35->N14+N35->N15+N35->N16+N35->N17+N35->N18+N35->N19+N35->N20+N35->N21+N35->N22+N35->N23+N35->N24+N35->N25+N35->N26+N35->N27+N35->N28+N35->N29+N35->N30+N35->N31+N35->N32+N35->N33+N35->N34+N35->N35+N36->N0+N36->N1+N36->N2+N36->N3+N36->N4+N36->N5+N36->N6+N36->N7+N36->N8+N36->N9+N36->N10+N36->N11+N36->N12+N36->N13+N36->N14+N36->N15+N36->N16+N36->N17+N36->N18+N36->N19+N36->N20+N36->N21+N36->N22+N36->N23+N36->N24+N36->N25+N36->N26+N36->N27+N36->N28+N36->N29+N36->N30+N36->N31+N36->N32+N36->N33+N36->N34+N36->N35+N36->N36+N37->N0+N37->N1+N37->N2+N37->N3+N37->N4+N37->N5+N37->N6+N37->N7+N37->N8+N37->N9+N37->N10+N37->N11+N37->N12+N37->N13+N37->N14+N37->N15+N37->N16+N37->N17+N37->N18+N37->N19+N37->N20+N37->N21+N37->N22+N37->N23+N37->N24+N37->N25+N37->N26+N37->N27+N37->N28+N37->N29+N37->N30+N37->N31+N37->N32+N37->N33+N37->N34+N37->N35+N37->N36+N37->N37+N38->N0+N38->N1+N38->N2+N38->N3+N38->N4+N38->N5+N38->N6+N38->N7+N38->N8+N38->N9+N38->N10+N38->N11+N38->N12+N38->N13+N38->N14+N38->N15+N38->N16+N38->N17+N38->N18+N38->N19+N38->N20+N38->N21+N38->N22+N38->N23+N38->N24+N38->N25+N38->N26+N38->N27+N38->N28+N38->N29+N38->N30+N38->N31+N38->N32+N38->N33+N38->N34+N38->N35+N38->N36+N38->N37+N38->N38 }
fact { QF.bparent_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13+N14->N0+N14->N1+N14->N2+N14->N3+N14->N4+N14->N5+N14->N6+N14->N7+N14->N8+N14->N9+N14->N10+N14->N11+N14->N12+N14->N13+N14->N14+N15->N0+N15->N1+N15->N2+N15->N3+N15->N4+N15->N5+N15->N6+N15->N7+N15->N8+N15->N9+N15->N10+N15->N11+N15->N12+N15->N13+N15->N14+N15->N15+N16->N0+N16->N1+N16->N2+N16->N3+N16->N4+N16->N5+N16->N6+N16->N7+N16->N8+N16->N9+N16->N10+N16->N11+N16->N12+N16->N13+N16->N14+N16->N15+N16->N16+N17->N0+N17->N1+N17->N2+N17->N3+N17->N4+N17->N5+N17->N6+N17->N7+N17->N8+N17->N9+N17->N10+N17->N11+N17->N12+N17->N13+N17->N14+N17->N15+N17->N16+N17->N17+N18->N0+N18->N1+N18->N2+N18->N3+N18->N4+N18->N5+N18->N6+N18->N7+N18->N8+N18->N9+N18->N10+N18->N11+N18->N12+N18->N13+N18->N14+N18->N15+N18->N16+N18->N17+N18->N18+N19->N0+N19->N1+N19->N2+N19->N3+N19->N4+N19->N5+N19->N6+N19->N7+N19->N8+N19->N9+N19->N10+N19->N11+N19->N12+N19->N13+N19->N14+N19->N15+N19->N16+N19->N17+N19->N18+N19->N19+N20->N0+N20->N1+N20->N2+N20->N3+N20->N4+N20->N5+N20->N6+N20->N7+N20->N8+N20->N9+N20->N10+N20->N11+N20->N12+N20->N13+N20->N14+N20->N15+N20->N16+N20->N17+N20->N18+N20->N19+N20->N20+N21->N0+N21->N1+N21->N2+N21->N3+N21->N4+N21->N5+N21->N6+N21->N7+N21->N8+N21->N9+N21->N10+N21->N11+N21->N12+N21->N13+N21->N14+N21->N15+N21->N16+N21->N17+N21->N18+N21->N19+N21->N20+N21->N21+N22->N0+N22->N1+N22->N2+N22->N3+N22->N4+N22->N5+N22->N6+N22->N7+N22->N8+N22->N9+N22->N10+N22->N11+N22->N12+N22->N13+N22->N14+N22->N15+N22->N16+N22->N17+N22->N18+N22->N19+N22->N20+N22->N21+N22->N22+N23->N0+N23->N1+N23->N2+N23->N3+N23->N4+N23->N5+N23->N6+N23->N7+N23->N8+N23->N9+N23->N10+N23->N11+N23->N12+N23->N13+N23->N14+N23->N15+N23->N16+N23->N17+N23->N18+N23->N19+N23->N20+N23->N21+N23->N22+N23->N23+N24->N0+N24->N1+N24->N2+N24->N3+N24->N4+N24->N5+N24->N6+N24->N7+N24->N8+N24->N9+N24->N10+N24->N11+N24->N12+N24->N13+N24->N14+N24->N15+N24->N16+N24->N17+N24->N18+N24->N19+N24->N20+N24->N21+N24->N22+N24->N23+N24->N24+N25->N0+N25->N1+N25->N2+N25->N3+N25->N4+N25->N5+N25->N6+N25->N7+N25->N8+N25->N9+N25->N10+N25->N11+N25->N12+N25->N13+N25->N14+N25->N15+N25->N16+N25->N17+N25->N18+N25->N19+N25->N20+N25->N21+N25->N22+N25->N23+N25->N24+N25->N25+N26->N0+N26->N1+N26->N2+N26->N3+N26->N4+N26->N5+N26->N6+N26->N7+N26->N8+N26->N9+N26->N10+N26->N11+N26->N12+N26->N13+N26->N14+N26->N15+N26->N16+N26->N17+N26->N18+N26->N19+N26->N20+N26->N21+N26->N22+N26->N23+N26->N24+N26->N25+N26->N26+N27->N0+N27->N1+N27->N2+N27->N3+N27->N4+N27->N5+N27->N6+N27->N7+N27->N8+N27->N9+N27->N10+N27->N11+N27->N12+N27->N13+N27->N14+N27->N15+N27->N16+N27->N17+N27->N18+N27->N19+N27->N20+N27->N21+N27->N22+N27->N23+N27->N24+N27->N25+N27->N26+N27->N27+N28->N0+N28->N1+N28->N2+N28->N3+N28->N4+N28->N5+N28->N6+N28->N7+N28->N8+N28->N9+N28->N10+N28->N11+N28->N12+N28->N13+N28->N14+N28->N15+N28->N16+N28->N17+N28->N18+N28->N19+N28->N20+N28->N21+N28->N22+N28->N23+N28->N24+N28->N25+N28->N26+N28->N27+N28->N28+N29->N0+N29->N1+N29->N2+N29->N3+N29->N4+N29->N5+N29->N6+N29->N7+N29->N8+N29->N9+N29->N10+N29->N11+N29->N12+N29->N13+N29->N14+N29->N15+N29->N16+N29->N17+N29->N18+N29->N19+N29->N20+N29->N21+N29->N22+N29->N23+N29->N24+N29->N25+N29->N26+N29->N27+N29->N28+N29->N29+N30->N0+N30->N1+N30->N2+N30->N3+N30->N4+N30->N5+N30->N6+N30->N7+N30->N8+N30->N9+N30->N10+N30->N11+N30->N12+N30->N13+N30->N14+N30->N15+N30->N16+N30->N17+N30->N18+N30->N19+N30->N20+N30->N21+N30->N22+N30->N23+N30->N24+N30->N25+N30->N26+N30->N27+N30->N28+N30->N29+N30->N30+N31->N0+N31->N1+N31->N2+N31->N3+N31->N4+N31->N5+N31->N6+N31->N7+N31->N8+N31->N9+N31->N10+N31->N11+N31->N12+N31->N13+N31->N14+N31->N15+N31->N16+N31->N17+N31->N18+N31->N19+N31->N20+N31->N21+N31->N22+N31->N23+N31->N24+N31->N25+N31->N26+N31->N27+N31->N28+N31->N29+N31->N30+N31->N31+N32->N0+N32->N1+N32->N2+N32->N3+N32->N4+N32->N5+N32->N6+N32->N7+N32->N8+N32->N9+N32->N10+N32->N11+N32->N12+N32->N13+N32->N14+N32->N15+N32->N16+N32->N17+N32->N18+N32->N19+N32->N20+N32->N21+N32->N22+N32->N23+N32->N24+N32->N25+N32->N26+N32->N27+N32->N28+N32->N29+N32->N30+N32->N31+N32->N32+N33->N0+N33->N1+N33->N2+N33->N3+N33->N4+N33->N5+N33->N6+N33->N7+N33->N8+N33->N9+N33->N10+N33->N11+N33->N12+N33->N13+N33->N14+N33->N15+N33->N16+N33->N17+N33->N18+N33->N19+N33->N20+N33->N21+N33->N22+N33->N23+N33->N24+N33->N25+N33->N26+N33->N27+N33->N28+N33->N29+N33->N30+N33->N31+N33->N32+N33->N33+N34->N0+N34->N1+N34->N2+N34->N3+N34->N4+N34->N5+N34->N6+N34->N7+N34->N8+N34->N9+N34->N10+N34->N11+N34->N12+N34->N13+N34->N14+N34->N15+N34->N16+N34->N17+N34->N18+N34->N19+N34->N20+N34->N21+N34->N22+N34->N23+N34->N24+N34->N25+N34->N26+N34->N27+N34->N28+N34->N29+N34->N30+N34->N31+N34->N32+N34->N33+N34->N34+N35->N0+N35->N1+N35->N2+N35->N3+N35->N4+N35->N5+N35->N6+N35->N7+N35->N8+N35->N9+N35->N10+N35->N11+N35->N12+N35->N13+N35->N14+N35->N15+N35->N16+N35->N17+N35->N18+N35->N19+N35->N20+N35->N21+N35->N22+N35->N23+N35->N24+N35->N25+N35->N26+N35->N27+N35->N28+N35->N29+N35->N30+N35->N31+N35->N32+N35->N33+N35->N34+N35->N35+N36->N0+N36->N1+N36->N2+N36->N3+N36->N4+N36->N5+N36->N6+N36->N7+N36->N8+N36->N9+N36->N10+N36->N11+N36->N12+N36->N13+N36->N14+N36->N15+N36->N16+N36->N17+N36->N18+N36->N19+N36->N20+N36->N21+N36->N22+N36->N23+N36->N24+N36->N25+N36->N26+N36->N27+N36->N28+N36->N29+N36->N30+N36->N31+N36->N32+N36->N33+N36->N34+N36->N35+N36->N36+N37->N0+N37->N1+N37->N2+N37->N3+N37->N4+N37->N5+N37->N6+N37->N7+N37->N8+N37->N9+N37->N10+N37->N11+N37->N12+N37->N13+N37->N14+N37->N15+N37->N16+N37->N17+N37->N18+N37->N19+N37->N20+N37->N21+N37->N22+N37->N23+N37->N24+N37->N25+N37->N26+N37->N27+N37->N28+N37->N29+N37->N30+N37->N31+N37->N32+N37->N33+N37->N34+N37->N35+N37->N36+N37->N37+N38->N0+N38->N1+N38->N2+N38->N3+N38->N4+N38->N5+N38->N6+N38->N7+N38->N8+N38->N9+N38->N10+N38->N11+N38->N12+N38->N13+N38->N14+N38->N15+N38->N16+N38->N17+N38->N18+N38->N19+N38->N20+N38->N21+N38->N22+N38->N23+N38->N24+N38->N25+N38->N26+N38->N27+N38->N28+N38->N29+N38->N30+N38->N31+N38->N32+N38->N33+N38->N34+N38->N35+N38->N36+N38->N37+N38->N38 }


fact {
	(QF.key_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->i329+N0->i3210+N0->i3211+N0->i3212+N0->i3213+N0->i3214+N0->i3215+N0->i3216+N0->i3217+N0->i3218+N0->i3219+N0->i3220+N0->i3221+N0->i3222+N0->i3223+N0->i3224+N0->i3225+N0->i3226+N0->i3227+N0->i3228+N0->i3229+N0->i3230+N0->i3231+N0->i3232+N0->i3233+N0->i3234+N0->i3235+N0->i3236+N0->i3237+N0->i3238+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->i329+N1->i3210+N1->i3211+N1->i3212+N1->i3213+N1->i3214+N1->i3215+N1->i3216+N1->i3217+N1->i3218+N1->i3219+N1->i3220+N1->i3221+N1->i3222+N1->i3223+N1->i3224+N1->i3225+N1->i3226+N1->i3227+N1->i3228+N1->i3229+N1->i3230+N1->i3231+N1->i3232+N1->i3233+N1->i3234+N1->i3235+N1->i3236+N1->i3237+N1->i3238+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->i329+N2->i3210+N2->i3211+N2->i3212+N2->i3213+N2->i3214+N2->i3215+N2->i3216+N2->i3217+N2->i3218+N2->i3219+N2->i3220+N2->i3221+N2->i3222+N2->i3223+N2->i3224+N2->i3225+N2->i3226+N2->i3227+N2->i3228+N2->i3229+N2->i3230+N2->i3231+N2->i3232+N2->i3233+N2->i3234+N2->i3235+N2->i3236+N2->i3237+N2->i3238+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->i329+N3->i3210+N3->i3211+N3->i3212+N3->i3213+N3->i3214+N3->i3215+N3->i3216+N3->i3217+N3->i3218+N3->i3219+N3->i3220+N3->i3221+N3->i3222+N3->i3223+N3->i3224+N3->i3225+N3->i3226+N3->i3227+N3->i3228+N3->i3229+N3->i3230+N3->i3231+N3->i3232+N3->i3233+N3->i3234+N3->i3235+N3->i3236+N3->i3237+N3->i3238+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->i329+N4->i3210+N4->i3211+N4->i3212+N4->i3213+N4->i3214+N4->i3215+N4->i3216+N4->i3217+N4->i3218+N4->i3219+N4->i3220+N4->i3221+N4->i3222+N4->i3223+N4->i3224+N4->i3225+N4->i3226+N4->i3227+N4->i3228+N4->i3229+N4->i3230+N4->i3231+N4->i3232+N4->i3233+N4->i3234+N4->i3235+N4->i3236+N4->i3237+N4->i3238+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->i329+N5->i3210+N5->i3211+N5->i3212+N5->i3213+N5->i3214+N5->i3215+N5->i3216+N5->i3217+N5->i3218+N5->i3219+N5->i3220+N5->i3221+N5->i3222+N5->i3223+N5->i3224+N5->i3225+N5->i3226+N5->i3227+N5->i3228+N5->i3229+N5->i3230+N5->i3231+N5->i3232+N5->i3233+N5->i3234+N5->i3235+N5->i3236+N5->i3237+N5->i3238+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->i329+N6->i3210+N6->i3211+N6->i3212+N6->i3213+N6->i3214+N6->i3215+N6->i3216+N6->i3217+N6->i3218+N6->i3219+N6->i3220+N6->i3221+N6->i3222+N6->i3223+N6->i3224+N6->i3225+N6->i3226+N6->i3227+N6->i3228+N6->i3229+N6->i3230+N6->i3231+N6->i3232+N6->i3233+N6->i3234+N6->i3235+N6->i3236+N6->i3237+N6->i3238+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->i329+N7->i3210+N7->i3211+N7->i3212+N7->i3213+N7->i3214+N7->i3215+N7->i3216+N7->i3217+N7->i3218+N7->i3219+N7->i3220+N7->i3221+N7->i3222+N7->i3223+N7->i3224+N7->i3225+N7->i3226+N7->i3227+N7->i3228+N7->i3229+N7->i3230+N7->i3231+N7->i3232+N7->i3233+N7->i3234+N7->i3235+N7->i3236+N7->i3237+N7->i3238+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->i329+N8->i3210+N8->i3211+N8->i3212+N8->i3213+N8->i3214+N8->i3215+N8->i3216+N8->i3217+N8->i3218+N8->i3219+N8->i3220+N8->i3221+N8->i3222+N8->i3223+N8->i3224+N8->i3225+N8->i3226+N8->i3227+N8->i3228+N8->i3229+N8->i3230+N8->i3231+N8->i3232+N8->i3233+N8->i3234+N8->i3235+N8->i3236+N8->i3237+N8->i3238+N8->null+N9->i320+N9->i321+N9->i322+N9->i323+N9->i324+N9->i325+N9->i326+N9->i327+N9->i328+N9->i329+N9->i3210+N9->i3211+N9->i3212+N9->i3213+N9->i3214+N9->i3215+N9->i3216+N9->i3217+N9->i3218+N9->i3219+N9->i3220+N9->i3221+N9->i3222+N9->i3223+N9->i3224+N9->i3225+N9->i3226+N9->i3227+N9->i3228+N9->i3229+N9->i3230+N9->i3231+N9->i3232+N9->i3233+N9->i3234+N9->i3235+N9->i3236+N9->i3237+N9->i3238+N9->null+N10->i320+N10->i321+N10->i322+N10->i323+N10->i324+N10->i325+N10->i326+N10->i327+N10->i328+N10->i329+N10->i3210+N10->i3211+N10->i3212+N10->i3213+N10->i3214+N10->i3215+N10->i3216+N10->i3217+N10->i3218+N10->i3219+N10->i3220+N10->i3221+N10->i3222+N10->i3223+N10->i3224+N10->i3225+N10->i3226+N10->i3227+N10->i3228+N10->i3229+N10->i3230+N10->i3231+N10->i3232+N10->i3233+N10->i3234+N10->i3235+N10->i3236+N10->i3237+N10->i3238+N10->null+N11->i320+N11->i321+N11->i322+N11->i323+N11->i324+N11->i325+N11->i326+N11->i327+N11->i328+N11->i329+N11->i3210+N11->i3211+N11->i3212+N11->i3213+N11->i3214+N11->i3215+N11->i3216+N11->i3217+N11->i3218+N11->i3219+N11->i3220+N11->i3221+N11->i3222+N11->i3223+N11->i3224+N11->i3225+N11->i3226+N11->i3227+N11->i3228+N11->i3229+N11->i3230+N11->i3231+N11->i3232+N11->i3233+N11->i3234+N11->i3235+N11->i3236+N11->i3237+N11->i3238+N11->null+N12->i320+N12->i321+N12->i322+N12->i323+N12->i324+N12->i325+N12->i326+N12->i327+N12->i328+N12->i329+N12->i3210+N12->i3211+N12->i3212+N12->i3213+N12->i3214+N12->i3215+N12->i3216+N12->i3217+N12->i3218+N12->i3219+N12->i3220+N12->i3221+N12->i3222+N12->i3223+N12->i3224+N12->i3225+N12->i3226+N12->i3227+N12->i3228+N12->i3229+N12->i3230+N12->i3231+N12->i3232+N12->i3233+N12->i3234+N12->i3235+N12->i3236+N12->i3237+N12->i3238+N12->null+N13->i320+N13->i321+N13->i322+N13->i323+N13->i324+N13->i325+N13->i326+N13->i327+N13->i328+N13->i329+N13->i3210+N13->i3211+N13->i3212+N13->i3213+N13->i3214+N13->i3215+N13->i3216+N13->i3217+N13->i3218+N13->i3219+N13->i3220+N13->i3221+N13->i3222+N13->i3223+N13->i3224+N13->i3225+N13->i3226+N13->i3227+N13->i3228+N13->i3229+N13->i3230+N13->i3231+N13->i3232+N13->i3233+N13->i3234+N13->i3235+N13->i3236+N13->i3237+N13->i3238+N13->null+N14->i320+N14->i321+N14->i322+N14->i323+N14->i324+N14->i325+N14->i326+N14->i327+N14->i328+N14->i329+N14->i3210+N14->i3211+N14->i3212+N14->i3213+N14->i3214+N14->i3215+N14->i3216+N14->i3217+N14->i3218+N14->i3219+N14->i3220+N14->i3221+N14->i3222+N14->i3223+N14->i3224+N14->i3225+N14->i3226+N14->i3227+N14->i3228+N14->i3229+N14->i3230+N14->i3231+N14->i3232+N14->i3233+N14->i3234+N14->i3235+N14->i3236+N14->i3237+N14->i3238+N14->null+N15->i320+N15->i321+N15->i322+N15->i323+N15->i324+N15->i325+N15->i326+N15->i327+N15->i328+N15->i329+N15->i3210+N15->i3211+N15->i3212+N15->i3213+N15->i3214+N15->i3215+N15->i3216+N15->i3217+N15->i3218+N15->i3219+N15->i3220+N15->i3221+N15->i3222+N15->i3223+N15->i3224+N15->i3225+N15->i3226+N15->i3227+N15->i3228+N15->i3229+N15->i3230+N15->i3231+N15->i3232+N15->i3233+N15->i3234+N15->i3235+N15->i3236+N15->i3237+N15->i3238+N15->null+N16->i320+N16->i321+N16->i322+N16->i323+N16->i324+N16->i325+N16->i326+N16->i327+N16->i328+N16->i329+N16->i3210+N16->i3211+N16->i3212+N16->i3213+N16->i3214+N16->i3215+N16->i3216+N16->i3217+N16->i3218+N16->i3219+N16->i3220+N16->i3221+N16->i3222+N16->i3223+N16->i3224+N16->i3225+N16->i3226+N16->i3227+N16->i3228+N16->i3229+N16->i3230+N16->i3231+N16->i3232+N16->i3233+N16->i3234+N16->i3235+N16->i3236+N16->i3237+N16->i3238+N16->null+N17->i320+N17->i321+N17->i322+N17->i323+N17->i324+N17->i325+N17->i326+N17->i327+N17->i328+N17->i329+N17->i3210+N17->i3211+N17->i3212+N17->i3213+N17->i3214+N17->i3215+N17->i3216+N17->i3217+N17->i3218+N17->i3219+N17->i3220+N17->i3221+N17->i3222+N17->i3223+N17->i3224+N17->i3225+N17->i3226+N17->i3227+N17->i3228+N17->i3229+N17->i3230+N17->i3231+N17->i3232+N17->i3233+N17->i3234+N17->i3235+N17->i3236+N17->i3237+N17->i3238+N17->null+N18->i320+N18->i321+N18->i322+N18->i323+N18->i324+N18->i325+N18->i326+N18->i327+N18->i328+N18->i329+N18->i3210+N18->i3211+N18->i3212+N18->i3213+N18->i3214+N18->i3215+N18->i3216+N18->i3217+N18->i3218+N18->i3219+N18->i3220+N18->i3221+N18->i3222+N18->i3223+N18->i3224+N18->i3225+N18->i3226+N18->i3227+N18->i3228+N18->i3229+N18->i3230+N18->i3231+N18->i3232+N18->i3233+N18->i3234+N18->i3235+N18->i3236+N18->i3237+N18->i3238+N18->null+N19->i320+N19->i321+N19->i322+N19->i323+N19->i324+N19->i325+N19->i326+N19->i327+N19->i328+N19->i329+N19->i3210+N19->i3211+N19->i3212+N19->i3213+N19->i3214+N19->i3215+N19->i3216+N19->i3217+N19->i3218+N19->i3219+N19->i3220+N19->i3221+N19->i3222+N19->i3223+N19->i3224+N19->i3225+N19->i3226+N19->i3227+N19->i3228+N19->i3229+N19->i3230+N19->i3231+N19->i3232+N19->i3233+N19->i3234+N19->i3235+N19->i3236+N19->i3237+N19->i3238+N19->null+N20->i320+N20->i321+N20->i322+N20->i323+N20->i324+N20->i325+N20->i326+N20->i327+N20->i328+N20->i329+N20->i3210+N20->i3211+N20->i3212+N20->i3213+N20->i3214+N20->i3215+N20->i3216+N20->i3217+N20->i3218+N20->i3219+N20->i3220+N20->i3221+N20->i3222+N20->i3223+N20->i3224+N20->i3225+N20->i3226+N20->i3227+N20->i3228+N20->i3229+N20->i3230+N20->i3231+N20->i3232+N20->i3233+N20->i3234+N20->i3235+N20->i3236+N20->i3237+N20->i3238+N20->null+N21->i320+N21->i321+N21->i322+N21->i323+N21->i324+N21->i325+N21->i326+N21->i327+N21->i328+N21->i329+N21->i3210+N21->i3211+N21->i3212+N21->i3213+N21->i3214+N21->i3215+N21->i3216+N21->i3217+N21->i3218+N21->i3219+N21->i3220+N21->i3221+N21->i3222+N21->i3223+N21->i3224+N21->i3225+N21->i3226+N21->i3227+N21->i3228+N21->i3229+N21->i3230+N21->i3231+N21->i3232+N21->i3233+N21->i3234+N21->i3235+N21->i3236+N21->i3237+N21->i3238+N21->null+N22->i320+N22->i321+N22->i322+N22->i323+N22->i324+N22->i325+N22->i326+N22->i327+N22->i328+N22->i329+N22->i3210+N22->i3211+N22->i3212+N22->i3213+N22->i3214+N22->i3215+N22->i3216+N22->i3217+N22->i3218+N22->i3219+N22->i3220+N22->i3221+N22->i3222+N22->i3223+N22->i3224+N22->i3225+N22->i3226+N22->i3227+N22->i3228+N22->i3229+N22->i3230+N22->i3231+N22->i3232+N22->i3233+N22->i3234+N22->i3235+N22->i3236+N22->i3237+N22->i3238+N22->null+N23->i320+N23->i321+N23->i322+N23->i323+N23->i324+N23->i325+N23->i326+N23->i327+N23->i328+N23->i329+N23->i3210+N23->i3211+N23->i3212+N23->i3213+N23->i3214+N23->i3215+N23->i3216+N23->i3217+N23->i3218+N23->i3219+N23->i3220+N23->i3221+N23->i3222+N23->i3223+N23->i3224+N23->i3225+N23->i3226+N23->i3227+N23->i3228+N23->i3229+N23->i3230+N23->i3231+N23->i3232+N23->i3233+N23->i3234+N23->i3235+N23->i3236+N23->i3237+N23->i3238+N23->null+N24->i320+N24->i321+N24->i322+N24->i323+N24->i324+N24->i325+N24->i326+N24->i327+N24->i328+N24->i329+N24->i3210+N24->i3211+N24->i3212+N24->i3213+N24->i3214+N24->i3215+N24->i3216+N24->i3217+N24->i3218+N24->i3219+N24->i3220+N24->i3221+N24->i3222+N24->i3223+N24->i3224+N24->i3225+N24->i3226+N24->i3227+N24->i3228+N24->i3229+N24->i3230+N24->i3231+N24->i3232+N24->i3233+N24->i3234+N24->i3235+N24->i3236+N24->i3237+N24->i3238+N24->null+N25->i320+N25->i321+N25->i322+N25->i323+N25->i324+N25->i325+N25->i326+N25->i327+N25->i328+N25->i329+N25->i3210+N25->i3211+N25->i3212+N25->i3213+N25->i3214+N25->i3215+N25->i3216+N25->i3217+N25->i3218+N25->i3219+N25->i3220+N25->i3221+N25->i3222+N25->i3223+N25->i3224+N25->i3225+N25->i3226+N25->i3227+N25->i3228+N25->i3229+N25->i3230+N25->i3231+N25->i3232+N25->i3233+N25->i3234+N25->i3235+N25->i3236+N25->i3237+N25->i3238+N25->null+N26->i320+N26->i321+N26->i322+N26->i323+N26->i324+N26->i325+N26->i326+N26->i327+N26->i328+N26->i329+N26->i3210+N26->i3211+N26->i3212+N26->i3213+N26->i3214+N26->i3215+N26->i3216+N26->i3217+N26->i3218+N26->i3219+N26->i3220+N26->i3221+N26->i3222+N26->i3223+N26->i3224+N26->i3225+N26->i3226+N26->i3227+N26->i3228+N26->i3229+N26->i3230+N26->i3231+N26->i3232+N26->i3233+N26->i3234+N26->i3235+N26->i3236+N26->i3237+N26->i3238+N26->null+N27->i320+N27->i321+N27->i322+N27->i323+N27->i324+N27->i325+N27->i326+N27->i327+N27->i328+N27->i329+N27->i3210+N27->i3211+N27->i3212+N27->i3213+N27->i3214+N27->i3215+N27->i3216+N27->i3217+N27->i3218+N27->i3219+N27->i3220+N27->i3221+N27->i3222+N27->i3223+N27->i3224+N27->i3225+N27->i3226+N27->i3227+N27->i3228+N27->i3229+N27->i3230+N27->i3231+N27->i3232+N27->i3233+N27->i3234+N27->i3235+N27->i3236+N27->i3237+N27->i3238+N27->null+N28->i320+N28->i321+N28->i322+N28->i323+N28->i324+N28->i325+N28->i326+N28->i327+N28->i328+N28->i329+N28->i3210+N28->i3211+N28->i3212+N28->i3213+N28->i3214+N28->i3215+N28->i3216+N28->i3217+N28->i3218+N28->i3219+N28->i3220+N28->i3221+N28->i3222+N28->i3223+N28->i3224+N28->i3225+N28->i3226+N28->i3227+N28->i3228+N28->i3229+N28->i3230+N28->i3231+N28->i3232+N28->i3233+N28->i3234+N28->i3235+N28->i3236+N28->i3237+N28->i3238+N28->null+N29->i320+N29->i321+N29->i322+N29->i323+N29->i324+N29->i325+N29->i326+N29->i327+N29->i328+N29->i329+N29->i3210+N29->i3211+N29->i3212+N29->i3213+N29->i3214+N29->i3215+N29->i3216+N29->i3217+N29->i3218+N29->i3219+N29->i3220+N29->i3221+N29->i3222+N29->i3223+N29->i3224+N29->i3225+N29->i3226+N29->i3227+N29->i3228+N29->i3229+N29->i3230+N29->i3231+N29->i3232+N29->i3233+N29->i3234+N29->i3235+N29->i3236+N29->i3237+N29->i3238+N29->null+N30->i320+N30->i321+N30->i322+N30->i323+N30->i324+N30->i325+N30->i326+N30->i327+N30->i328+N30->i329+N30->i3210+N30->i3211+N30->i3212+N30->i3213+N30->i3214+N30->i3215+N30->i3216+N30->i3217+N30->i3218+N30->i3219+N30->i3220+N30->i3221+N30->i3222+N30->i3223+N30->i3224+N30->i3225+N30->i3226+N30->i3227+N30->i3228+N30->i3229+N30->i3230+N30->i3231+N30->i3232+N30->i3233+N30->i3234+N30->i3235+N30->i3236+N30->i3237+N30->i3238+N30->null+N31->i320+N31->i321+N31->i322+N31->i323+N31->i324+N31->i325+N31->i326+N31->i327+N31->i328+N31->i329+N31->i3210+N31->i3211+N31->i3212+N31->i3213+N31->i3214+N31->i3215+N31->i3216+N31->i3217+N31->i3218+N31->i3219+N31->i3220+N31->i3221+N31->i3222+N31->i3223+N31->i3224+N31->i3225+N31->i3226+N31->i3227+N31->i3228+N31->i3229+N31->i3230+N31->i3231+N31->i3232+N31->i3233+N31->i3234+N31->i3235+N31->i3236+N31->i3237+N31->i3238+N31->null+N32->i320+N32->i321+N32->i322+N32->i323+N32->i324+N32->i325+N32->i326+N32->i327+N32->i328+N32->i329+N32->i3210+N32->i3211+N32->i3212+N32->i3213+N32->i3214+N32->i3215+N32->i3216+N32->i3217+N32->i3218+N32->i3219+N32->i3220+N32->i3221+N32->i3222+N32->i3223+N32->i3224+N32->i3225+N32->i3226+N32->i3227+N32->i3228+N32->i3229+N32->i3230+N32->i3231+N32->i3232+N32->i3233+N32->i3234+N32->i3235+N32->i3236+N32->i3237+N32->i3238+N32->null+N33->i320+N33->i321+N33->i322+N33->i323+N33->i324+N33->i325+N33->i326+N33->i327+N33->i328+N33->i329+N33->i3210+N33->i3211+N33->i3212+N33->i3213+N33->i3214+N33->i3215+N33->i3216+N33->i3217+N33->i3218+N33->i3219+N33->i3220+N33->i3221+N33->i3222+N33->i3223+N33->i3224+N33->i3225+N33->i3226+N33->i3227+N33->i3228+N33->i3229+N33->i3230+N33->i3231+N33->i3232+N33->i3233+N33->i3234+N33->i3235+N33->i3236+N33->i3237+N33->i3238+N33->null+N34->i320+N34->i321+N34->i322+N34->i323+N34->i324+N34->i325+N34->i326+N34->i327+N34->i328+N34->i329+N34->i3210+N34->i3211+N34->i3212+N34->i3213+N34->i3214+N34->i3215+N34->i3216+N34->i3217+N34->i3218+N34->i3219+N34->i3220+N34->i3221+N34->i3222+N34->i3223+N34->i3224+N34->i3225+N34->i3226+N34->i3227+N34->i3228+N34->i3229+N34->i3230+N34->i3231+N34->i3232+N34->i3233+N34->i3234+N34->i3235+N34->i3236+N34->i3237+N34->i3238+N34->null+N35->i320+N35->i321+N35->i322+N35->i323+N35->i324+N35->i325+N35->i326+N35->i327+N35->i328+N35->i329+N35->i3210+N35->i3211+N35->i3212+N35->i3213+N35->i3214+N35->i3215+N35->i3216+N35->i3217+N35->i3218+N35->i3219+N35->i3220+N35->i3221+N35->i3222+N35->i3223+N35->i3224+N35->i3225+N35->i3226+N35->i3227+N35->i3228+N35->i3229+N35->i3230+N35->i3231+N35->i3232+N35->i3233+N35->i3234+N35->i3235+N35->i3236+N35->i3237+N35->i3238+N35->null+N36->i320+N36->i321+N36->i322+N36->i323+N36->i324+N36->i325+N36->i326+N36->i327+N36->i328+N36->i329+N36->i3210+N36->i3211+N36->i3212+N36->i3213+N36->i3214+N36->i3215+N36->i3216+N36->i3217+N36->i3218+N36->i3219+N36->i3220+N36->i3221+N36->i3222+N36->i3223+N36->i3224+N36->i3225+N36->i3226+N36->i3227+N36->i3228+N36->i3229+N36->i3230+N36->i3231+N36->i3232+N36->i3233+N36->i3234+N36->i3235+N36->i3236+N36->i3237+N36->i3238+N36->null+N37->i320+N37->i321+N37->i322+N37->i323+N37->i324+N37->i325+N37->i326+N37->i327+N37->i328+N37->i329+N37->i3210+N37->i3211+N37->i3212+N37->i3213+N37->i3214+N37->i3215+N37->i3216+N37->i3217+N37->i3218+N37->i3219+N37->i3220+N37->i3221+N37->i3222+N37->i3223+N37->i3224+N37->i3225+N37->i3226+N37->i3227+N37->i3228+N37->i3229+N37->i3230+N37->i3231+N37->i3232+N37->i3233+N37->i3234+N37->i3235+N37->i3236+N37->i3237+N37->i3238+N37->null+N38->i320+N38->i321+N38->i322+N38->i323+N38->i324+N38->i325+N38->i326+N38->i327+N38->i328+N38->i329+N38->i3210+N38->i3211+N38->i3212+N38->i3213+N38->i3214+N38->i3215+N38->i3216+N38->i3217+N38->i3218+N38->i3219+N38->i3220+N38->i3221+N38->i3222+N38->i3223+N38->i3224+N38->i3225+N38->i3226+N38->i3227+N38->i3228+N38->i3229+N38->i3230+N38->i3231+N38->i3232+N38->i3233+N38->i3234+N38->i3235+N38->i3236+N38->i3237+N38->i3238+N38->null
}


fact {
	(QF.size_0) in TreeSetIntVar->i320+TreeSetIntVar->i321+TreeSetIntVar->i322+TreeSetIntVar->i323+TreeSetIntVar->i324+TreeSetIntVar->i325+TreeSetIntVar->i326+TreeSetIntVar->i327+TreeSetIntVar->i328+TreeSetIntVar->i329+TreeSetIntVar->i3210+TreeSetIntVar->i3211+TreeSetIntVar->i3212+TreeSetIntVar->i3213+TreeSetIntVar->i3214+TreeSetIntVar->i3215+TreeSetIntVar->i3216+TreeSetIntVar->i3217+TreeSetIntVar->i3218+TreeSetIntVar->i3219+TreeSetIntVar->i3220+TreeSetIntVar->i3221+TreeSetIntVar->i3222+TreeSetIntVar->i3223+TreeSetIntVar->i3224+TreeSetIntVar->i3225+TreeSetIntVar->i3226+TreeSetIntVar->i3227+TreeSetIntVar->i3228+TreeSetIntVar->i3229+TreeSetIntVar->i3230+TreeSetIntVar->i3231+TreeSetIntVar->i3232+TreeSetIntVar->i3233+TreeSetIntVar->i3234+TreeSetIntVar->i3235+TreeSetIntVar->i3236+TreeSetIntVar->i3237+TreeSetIntVar->i3238+TreeSetIntVar->i3239
}


fact {
	(QF.blackHeight_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->i329+N0->i3210+N0->i3211+N0->i3212+N0->i3213+N0->i3214+N0->i3215+N0->i3216+N0->i3217+N0->i3218+N0->i3219+N0->i3220+N0->i3221+N0->i3222+N0->i3223+N0->i3224+N0->i3225+N0->i3226+N0->i3227+N0->i3228+N0->i3229+N0->i3230+N0->i3231+N0->i3232+N0->i3233+N0->i3234+N0->i3235+N0->i3236+N0->i3237+N0->i3238+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->i329+N1->i3210+N1->i3211+N1->i3212+N1->i3213+N1->i3214+N1->i3215+N1->i3216+N1->i3217+N1->i3218+N1->i3219+N1->i3220+N1->i3221+N1->i3222+N1->i3223+N1->i3224+N1->i3225+N1->i3226+N1->i3227+N1->i3228+N1->i3229+N1->i3230+N1->i3231+N1->i3232+N1->i3233+N1->i3234+N1->i3235+N1->i3236+N1->i3237+N1->i3238+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->i329+N2->i3210+N2->i3211+N2->i3212+N2->i3213+N2->i3214+N2->i3215+N2->i3216+N2->i3217+N2->i3218+N2->i3219+N2->i3220+N2->i3221+N2->i3222+N2->i3223+N2->i3224+N2->i3225+N2->i3226+N2->i3227+N2->i3228+N2->i3229+N2->i3230+N2->i3231+N2->i3232+N2->i3233+N2->i3234+N2->i3235+N2->i3236+N2->i3237+N2->i3238+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->i329+N3->i3210+N3->i3211+N3->i3212+N3->i3213+N3->i3214+N3->i3215+N3->i3216+N3->i3217+N3->i3218+N3->i3219+N3->i3220+N3->i3221+N3->i3222+N3->i3223+N3->i3224+N3->i3225+N3->i3226+N3->i3227+N3->i3228+N3->i3229+N3->i3230+N3->i3231+N3->i3232+N3->i3233+N3->i3234+N3->i3235+N3->i3236+N3->i3237+N3->i3238+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->i329+N4->i3210+N4->i3211+N4->i3212+N4->i3213+N4->i3214+N4->i3215+N4->i3216+N4->i3217+N4->i3218+N4->i3219+N4->i3220+N4->i3221+N4->i3222+N4->i3223+N4->i3224+N4->i3225+N4->i3226+N4->i3227+N4->i3228+N4->i3229+N4->i3230+N4->i3231+N4->i3232+N4->i3233+N4->i3234+N4->i3235+N4->i3236+N4->i3237+N4->i3238+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->i329+N5->i3210+N5->i3211+N5->i3212+N5->i3213+N5->i3214+N5->i3215+N5->i3216+N5->i3217+N5->i3218+N5->i3219+N5->i3220+N5->i3221+N5->i3222+N5->i3223+N5->i3224+N5->i3225+N5->i3226+N5->i3227+N5->i3228+N5->i3229+N5->i3230+N5->i3231+N5->i3232+N5->i3233+N5->i3234+N5->i3235+N5->i3236+N5->i3237+N5->i3238+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->i329+N6->i3210+N6->i3211+N6->i3212+N6->i3213+N6->i3214+N6->i3215+N6->i3216+N6->i3217+N6->i3218+N6->i3219+N6->i3220+N6->i3221+N6->i3222+N6->i3223+N6->i3224+N6->i3225+N6->i3226+N6->i3227+N6->i3228+N6->i3229+N6->i3230+N6->i3231+N6->i3232+N6->i3233+N6->i3234+N6->i3235+N6->i3236+N6->i3237+N6->i3238+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->i329+N7->i3210+N7->i3211+N7->i3212+N7->i3213+N7->i3214+N7->i3215+N7->i3216+N7->i3217+N7->i3218+N7->i3219+N7->i3220+N7->i3221+N7->i3222+N7->i3223+N7->i3224+N7->i3225+N7->i3226+N7->i3227+N7->i3228+N7->i3229+N7->i3230+N7->i3231+N7->i3232+N7->i3233+N7->i3234+N7->i3235+N7->i3236+N7->i3237+N7->i3238+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->i329+N8->i3210+N8->i3211+N8->i3212+N8->i3213+N8->i3214+N8->i3215+N8->i3216+N8->i3217+N8->i3218+N8->i3219+N8->i3220+N8->i3221+N8->i3222+N8->i3223+N8->i3224+N8->i3225+N8->i3226+N8->i3227+N8->i3228+N8->i3229+N8->i3230+N8->i3231+N8->i3232+N8->i3233+N8->i3234+N8->i3235+N8->i3236+N8->i3237+N8->i3238+N8->null+N9->i320+N9->i321+N9->i322+N9->i323+N9->i324+N9->i325+N9->i326+N9->i327+N9->i328+N9->i329+N9->i3210+N9->i3211+N9->i3212+N9->i3213+N9->i3214+N9->i3215+N9->i3216+N9->i3217+N9->i3218+N9->i3219+N9->i3220+N9->i3221+N9->i3222+N9->i3223+N9->i3224+N9->i3225+N9->i3226+N9->i3227+N9->i3228+N9->i3229+N9->i3230+N9->i3231+N9->i3232+N9->i3233+N9->i3234+N9->i3235+N9->i3236+N9->i3237+N9->i3238+N9->null+N10->i320+N10->i321+N10->i322+N10->i323+N10->i324+N10->i325+N10->i326+N10->i327+N10->i328+N10->i329+N10->i3210+N10->i3211+N10->i3212+N10->i3213+N10->i3214+N10->i3215+N10->i3216+N10->i3217+N10->i3218+N10->i3219+N10->i3220+N10->i3221+N10->i3222+N10->i3223+N10->i3224+N10->i3225+N10->i3226+N10->i3227+N10->i3228+N10->i3229+N10->i3230+N10->i3231+N10->i3232+N10->i3233+N10->i3234+N10->i3235+N10->i3236+N10->i3237+N10->i3238+N10->null+N11->i320+N11->i321+N11->i322+N11->i323+N11->i324+N11->i325+N11->i326+N11->i327+N11->i328+N11->i329+N11->i3210+N11->i3211+N11->i3212+N11->i3213+N11->i3214+N11->i3215+N11->i3216+N11->i3217+N11->i3218+N11->i3219+N11->i3220+N11->i3221+N11->i3222+N11->i3223+N11->i3224+N11->i3225+N11->i3226+N11->i3227+N11->i3228+N11->i3229+N11->i3230+N11->i3231+N11->i3232+N11->i3233+N11->i3234+N11->i3235+N11->i3236+N11->i3237+N11->i3238+N11->null+N12->i320+N12->i321+N12->i322+N12->i323+N12->i324+N12->i325+N12->i326+N12->i327+N12->i328+N12->i329+N12->i3210+N12->i3211+N12->i3212+N12->i3213+N12->i3214+N12->i3215+N12->i3216+N12->i3217+N12->i3218+N12->i3219+N12->i3220+N12->i3221+N12->i3222+N12->i3223+N12->i3224+N12->i3225+N12->i3226+N12->i3227+N12->i3228+N12->i3229+N12->i3230+N12->i3231+N12->i3232+N12->i3233+N12->i3234+N12->i3235+N12->i3236+N12->i3237+N12->i3238+N12->null+N13->i320+N13->i321+N13->i322+N13->i323+N13->i324+N13->i325+N13->i326+N13->i327+N13->i328+N13->i329+N13->i3210+N13->i3211+N13->i3212+N13->i3213+N13->i3214+N13->i3215+N13->i3216+N13->i3217+N13->i3218+N13->i3219+N13->i3220+N13->i3221+N13->i3222+N13->i3223+N13->i3224+N13->i3225+N13->i3226+N13->i3227+N13->i3228+N13->i3229+N13->i3230+N13->i3231+N13->i3232+N13->i3233+N13->i3234+N13->i3235+N13->i3236+N13->i3237+N13->i3238+N13->null+N14->i320+N14->i321+N14->i322+N14->i323+N14->i324+N14->i325+N14->i326+N14->i327+N14->i328+N14->i329+N14->i3210+N14->i3211+N14->i3212+N14->i3213+N14->i3214+N14->i3215+N14->i3216+N14->i3217+N14->i3218+N14->i3219+N14->i3220+N14->i3221+N14->i3222+N14->i3223+N14->i3224+N14->i3225+N14->i3226+N14->i3227+N14->i3228+N14->i3229+N14->i3230+N14->i3231+N14->i3232+N14->i3233+N14->i3234+N14->i3235+N14->i3236+N14->i3237+N14->i3238+N14->null+N15->i320+N15->i321+N15->i322+N15->i323+N15->i324+N15->i325+N15->i326+N15->i327+N15->i328+N15->i329+N15->i3210+N15->i3211+N15->i3212+N15->i3213+N15->i3214+N15->i3215+N15->i3216+N15->i3217+N15->i3218+N15->i3219+N15->i3220+N15->i3221+N15->i3222+N15->i3223+N15->i3224+N15->i3225+N15->i3226+N15->i3227+N15->i3228+N15->i3229+N15->i3230+N15->i3231+N15->i3232+N15->i3233+N15->i3234+N15->i3235+N15->i3236+N15->i3237+N15->i3238+N15->null+N16->i320+N16->i321+N16->i322+N16->i323+N16->i324+N16->i325+N16->i326+N16->i327+N16->i328+N16->i329+N16->i3210+N16->i3211+N16->i3212+N16->i3213+N16->i3214+N16->i3215+N16->i3216+N16->i3217+N16->i3218+N16->i3219+N16->i3220+N16->i3221+N16->i3222+N16->i3223+N16->i3224+N16->i3225+N16->i3226+N16->i3227+N16->i3228+N16->i3229+N16->i3230+N16->i3231+N16->i3232+N16->i3233+N16->i3234+N16->i3235+N16->i3236+N16->i3237+N16->i3238+N16->null+N17->i320+N17->i321+N17->i322+N17->i323+N17->i324+N17->i325+N17->i326+N17->i327+N17->i328+N17->i329+N17->i3210+N17->i3211+N17->i3212+N17->i3213+N17->i3214+N17->i3215+N17->i3216+N17->i3217+N17->i3218+N17->i3219+N17->i3220+N17->i3221+N17->i3222+N17->i3223+N17->i3224+N17->i3225+N17->i3226+N17->i3227+N17->i3228+N17->i3229+N17->i3230+N17->i3231+N17->i3232+N17->i3233+N17->i3234+N17->i3235+N17->i3236+N17->i3237+N17->i3238+N17->null+N18->i320+N18->i321+N18->i322+N18->i323+N18->i324+N18->i325+N18->i326+N18->i327+N18->i328+N18->i329+N18->i3210+N18->i3211+N18->i3212+N18->i3213+N18->i3214+N18->i3215+N18->i3216+N18->i3217+N18->i3218+N18->i3219+N18->i3220+N18->i3221+N18->i3222+N18->i3223+N18->i3224+N18->i3225+N18->i3226+N18->i3227+N18->i3228+N18->i3229+N18->i3230+N18->i3231+N18->i3232+N18->i3233+N18->i3234+N18->i3235+N18->i3236+N18->i3237+N18->i3238+N18->null+N19->i320+N19->i321+N19->i322+N19->i323+N19->i324+N19->i325+N19->i326+N19->i327+N19->i328+N19->i329+N19->i3210+N19->i3211+N19->i3212+N19->i3213+N19->i3214+N19->i3215+N19->i3216+N19->i3217+N19->i3218+N19->i3219+N19->i3220+N19->i3221+N19->i3222+N19->i3223+N19->i3224+N19->i3225+N19->i3226+N19->i3227+N19->i3228+N19->i3229+N19->i3230+N19->i3231+N19->i3232+N19->i3233+N19->i3234+N19->i3235+N19->i3236+N19->i3237+N19->i3238+N19->null+N20->i320+N20->i321+N20->i322+N20->i323+N20->i324+N20->i325+N20->i326+N20->i327+N20->i328+N20->i329+N20->i3210+N20->i3211+N20->i3212+N20->i3213+N20->i3214+N20->i3215+N20->i3216+N20->i3217+N20->i3218+N20->i3219+N20->i3220+N20->i3221+N20->i3222+N20->i3223+N20->i3224+N20->i3225+N20->i3226+N20->i3227+N20->i3228+N20->i3229+N20->i3230+N20->i3231+N20->i3232+N20->i3233+N20->i3234+N20->i3235+N20->i3236+N20->i3237+N20->i3238+N20->null+N21->i320+N21->i321+N21->i322+N21->i323+N21->i324+N21->i325+N21->i326+N21->i327+N21->i328+N21->i329+N21->i3210+N21->i3211+N21->i3212+N21->i3213+N21->i3214+N21->i3215+N21->i3216+N21->i3217+N21->i3218+N21->i3219+N21->i3220+N21->i3221+N21->i3222+N21->i3223+N21->i3224+N21->i3225+N21->i3226+N21->i3227+N21->i3228+N21->i3229+N21->i3230+N21->i3231+N21->i3232+N21->i3233+N21->i3234+N21->i3235+N21->i3236+N21->i3237+N21->i3238+N21->null+N22->i320+N22->i321+N22->i322+N22->i323+N22->i324+N22->i325+N22->i326+N22->i327+N22->i328+N22->i329+N22->i3210+N22->i3211+N22->i3212+N22->i3213+N22->i3214+N22->i3215+N22->i3216+N22->i3217+N22->i3218+N22->i3219+N22->i3220+N22->i3221+N22->i3222+N22->i3223+N22->i3224+N22->i3225+N22->i3226+N22->i3227+N22->i3228+N22->i3229+N22->i3230+N22->i3231+N22->i3232+N22->i3233+N22->i3234+N22->i3235+N22->i3236+N22->i3237+N22->i3238+N22->null+N23->i320+N23->i321+N23->i322+N23->i323+N23->i324+N23->i325+N23->i326+N23->i327+N23->i328+N23->i329+N23->i3210+N23->i3211+N23->i3212+N23->i3213+N23->i3214+N23->i3215+N23->i3216+N23->i3217+N23->i3218+N23->i3219+N23->i3220+N23->i3221+N23->i3222+N23->i3223+N23->i3224+N23->i3225+N23->i3226+N23->i3227+N23->i3228+N23->i3229+N23->i3230+N23->i3231+N23->i3232+N23->i3233+N23->i3234+N23->i3235+N23->i3236+N23->i3237+N23->i3238+N23->null+N24->i320+N24->i321+N24->i322+N24->i323+N24->i324+N24->i325+N24->i326+N24->i327+N24->i328+N24->i329+N24->i3210+N24->i3211+N24->i3212+N24->i3213+N24->i3214+N24->i3215+N24->i3216+N24->i3217+N24->i3218+N24->i3219+N24->i3220+N24->i3221+N24->i3222+N24->i3223+N24->i3224+N24->i3225+N24->i3226+N24->i3227+N24->i3228+N24->i3229+N24->i3230+N24->i3231+N24->i3232+N24->i3233+N24->i3234+N24->i3235+N24->i3236+N24->i3237+N24->i3238+N24->null+N25->i320+N25->i321+N25->i322+N25->i323+N25->i324+N25->i325+N25->i326+N25->i327+N25->i328+N25->i329+N25->i3210+N25->i3211+N25->i3212+N25->i3213+N25->i3214+N25->i3215+N25->i3216+N25->i3217+N25->i3218+N25->i3219+N25->i3220+N25->i3221+N25->i3222+N25->i3223+N25->i3224+N25->i3225+N25->i3226+N25->i3227+N25->i3228+N25->i3229+N25->i3230+N25->i3231+N25->i3232+N25->i3233+N25->i3234+N25->i3235+N25->i3236+N25->i3237+N25->i3238+N25->null+N26->i320+N26->i321+N26->i322+N26->i323+N26->i324+N26->i325+N26->i326+N26->i327+N26->i328+N26->i329+N26->i3210+N26->i3211+N26->i3212+N26->i3213+N26->i3214+N26->i3215+N26->i3216+N26->i3217+N26->i3218+N26->i3219+N26->i3220+N26->i3221+N26->i3222+N26->i3223+N26->i3224+N26->i3225+N26->i3226+N26->i3227+N26->i3228+N26->i3229+N26->i3230+N26->i3231+N26->i3232+N26->i3233+N26->i3234+N26->i3235+N26->i3236+N26->i3237+N26->i3238+N26->null+N27->i320+N27->i321+N27->i322+N27->i323+N27->i324+N27->i325+N27->i326+N27->i327+N27->i328+N27->i329+N27->i3210+N27->i3211+N27->i3212+N27->i3213+N27->i3214+N27->i3215+N27->i3216+N27->i3217+N27->i3218+N27->i3219+N27->i3220+N27->i3221+N27->i3222+N27->i3223+N27->i3224+N27->i3225+N27->i3226+N27->i3227+N27->i3228+N27->i3229+N27->i3230+N27->i3231+N27->i3232+N27->i3233+N27->i3234+N27->i3235+N27->i3236+N27->i3237+N27->i3238+N27->null+N28->i320+N28->i321+N28->i322+N28->i323+N28->i324+N28->i325+N28->i326+N28->i327+N28->i328+N28->i329+N28->i3210+N28->i3211+N28->i3212+N28->i3213+N28->i3214+N28->i3215+N28->i3216+N28->i3217+N28->i3218+N28->i3219+N28->i3220+N28->i3221+N28->i3222+N28->i3223+N28->i3224+N28->i3225+N28->i3226+N28->i3227+N28->i3228+N28->i3229+N28->i3230+N28->i3231+N28->i3232+N28->i3233+N28->i3234+N28->i3235+N28->i3236+N28->i3237+N28->i3238+N28->null+N29->i320+N29->i321+N29->i322+N29->i323+N29->i324+N29->i325+N29->i326+N29->i327+N29->i328+N29->i329+N29->i3210+N29->i3211+N29->i3212+N29->i3213+N29->i3214+N29->i3215+N29->i3216+N29->i3217+N29->i3218+N29->i3219+N29->i3220+N29->i3221+N29->i3222+N29->i3223+N29->i3224+N29->i3225+N29->i3226+N29->i3227+N29->i3228+N29->i3229+N29->i3230+N29->i3231+N29->i3232+N29->i3233+N29->i3234+N29->i3235+N29->i3236+N29->i3237+N29->i3238+N29->null+N30->i320+N30->i321+N30->i322+N30->i323+N30->i324+N30->i325+N30->i326+N30->i327+N30->i328+N30->i329+N30->i3210+N30->i3211+N30->i3212+N30->i3213+N30->i3214+N30->i3215+N30->i3216+N30->i3217+N30->i3218+N30->i3219+N30->i3220+N30->i3221+N30->i3222+N30->i3223+N30->i3224+N30->i3225+N30->i3226+N30->i3227+N30->i3228+N30->i3229+N30->i3230+N30->i3231+N30->i3232+N30->i3233+N30->i3234+N30->i3235+N30->i3236+N30->i3237+N30->i3238+N30->null+N31->i320+N31->i321+N31->i322+N31->i323+N31->i324+N31->i325+N31->i326+N31->i327+N31->i328+N31->i329+N31->i3210+N31->i3211+N31->i3212+N31->i3213+N31->i3214+N31->i3215+N31->i3216+N31->i3217+N31->i3218+N31->i3219+N31->i3220+N31->i3221+N31->i3222+N31->i3223+N31->i3224+N31->i3225+N31->i3226+N31->i3227+N31->i3228+N31->i3229+N31->i3230+N31->i3231+N31->i3232+N31->i3233+N31->i3234+N31->i3235+N31->i3236+N31->i3237+N31->i3238+N31->null+N32->i320+N32->i321+N32->i322+N32->i323+N32->i324+N32->i325+N32->i326+N32->i327+N32->i328+N32->i329+N32->i3210+N32->i3211+N32->i3212+N32->i3213+N32->i3214+N32->i3215+N32->i3216+N32->i3217+N32->i3218+N32->i3219+N32->i3220+N32->i3221+N32->i3222+N32->i3223+N32->i3224+N32->i3225+N32->i3226+N32->i3227+N32->i3228+N32->i3229+N32->i3230+N32->i3231+N32->i3232+N32->i3233+N32->i3234+N32->i3235+N32->i3236+N32->i3237+N32->i3238+N32->null+N33->i320+N33->i321+N33->i322+N33->i323+N33->i324+N33->i325+N33->i326+N33->i327+N33->i328+N33->i329+N33->i3210+N33->i3211+N33->i3212+N33->i3213+N33->i3214+N33->i3215+N33->i3216+N33->i3217+N33->i3218+N33->i3219+N33->i3220+N33->i3221+N33->i3222+N33->i3223+N33->i3224+N33->i3225+N33->i3226+N33->i3227+N33->i3228+N33->i3229+N33->i3230+N33->i3231+N33->i3232+N33->i3233+N33->i3234+N33->i3235+N33->i3236+N33->i3237+N33->i3238+N33->null+N34->i320+N34->i321+N34->i322+N34->i323+N34->i324+N34->i325+N34->i326+N34->i327+N34->i328+N34->i329+N34->i3210+N34->i3211+N34->i3212+N34->i3213+N34->i3214+N34->i3215+N34->i3216+N34->i3217+N34->i3218+N34->i3219+N34->i3220+N34->i3221+N34->i3222+N34->i3223+N34->i3224+N34->i3225+N34->i3226+N34->i3227+N34->i3228+N34->i3229+N34->i3230+N34->i3231+N34->i3232+N34->i3233+N34->i3234+N34->i3235+N34->i3236+N34->i3237+N34->i3238+N34->null+N35->i320+N35->i321+N35->i322+N35->i323+N35->i324+N35->i325+N35->i326+N35->i327+N35->i328+N35->i329+N35->i3210+N35->i3211+N35->i3212+N35->i3213+N35->i3214+N35->i3215+N35->i3216+N35->i3217+N35->i3218+N35->i3219+N35->i3220+N35->i3221+N35->i3222+N35->i3223+N35->i3224+N35->i3225+N35->i3226+N35->i3227+N35->i3228+N35->i3229+N35->i3230+N35->i3231+N35->i3232+N35->i3233+N35->i3234+N35->i3235+N35->i3236+N35->i3237+N35->i3238+N35->null+N36->i320+N36->i321+N36->i322+N36->i323+N36->i324+N36->i325+N36->i326+N36->i327+N36->i328+N36->i329+N36->i3210+N36->i3211+N36->i3212+N36->i3213+N36->i3214+N36->i3215+N36->i3216+N36->i3217+N36->i3218+N36->i3219+N36->i3220+N36->i3221+N36->i3222+N36->i3223+N36->i3224+N36->i3225+N36->i3226+N36->i3227+N36->i3228+N36->i3229+N36->i3230+N36->i3231+N36->i3232+N36->i3233+N36->i3234+N36->i3235+N36->i3236+N36->i3237+N36->i3238+N36->null+N37->i320+N37->i321+N37->i322+N37->i323+N37->i324+N37->i325+N37->i326+N37->i327+N37->i328+N37->i329+N37->i3210+N37->i3211+N37->i3212+N37->i3213+N37->i3214+N37->i3215+N37->i3216+N37->i3217+N37->i3218+N37->i3219+N37->i3220+N37->i3221+N37->i3222+N37->i3223+N37->i3224+N37->i3225+N37->i3226+N37->i3227+N37->i3228+N37->i3229+N37->i3230+N37->i3231+N37->i3232+N37->i3233+N37->i3234+N37->i3235+N37->i3236+N37->i3237+N37->i3238+N37->null+N38->i320+N38->i321+N38->i322+N38->i323+N38->i324+N38->i325+N38->i326+N38->i327+N38->i328+N38->i329+N38->i3210+N38->i3211+N38->i3212+N38->i3213+N38->i3214+N38->i3215+N38->i3216+N38->i3217+N38->i3218+N38->i3219+N38->i3220+N38->i3221+N38->i3222+N38->i3223+N38->i3224+N38->i3225+N38->i3226+N38->i3227+N38->i3228+N38->i3229+N38->i3230+N38->i3231+N38->i3232+N38->i3233+N38->i3234+N38->i3235+N38->i3236+N38->i3237+N38->i3238+N38->null
}




fun node_max[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38) {
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
   +
   N23->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N24->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23)
   +
   N25->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24)
   +
   N26->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25)
   +
   N27->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26)
   +
   N28->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27)
   +
   N29->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28)
   +
   N30->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29)
   +
   N31->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30)
   +
   N32->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31)
   +
   N33->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32)
   +
   N34->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33)
   +
   N35->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34)
   +
   N36->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35)
   +
   N37->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36)
   +
   N38->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37)
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
	  (m = N22 and size = i3223) or
	  (m = N23 and size = i3224) or
	  (m = N24 and size = i3225) or
	  (m = N25 and size = i3226) or
	  (m = N26 and size = i3227) or
	  (m = N27 and size = i3228) or
	  (m = N28 and size = i3229) or
	  (m = N29 and size = i3230) or
	  (m = N30 and size = i3231) or
	  (m = N31 and size = i3232) or
	  (m = N32 and size = i3233) or
	  (m = N33 and size = i3234) or
	  (m = N34 and size = i3235) or
	  (m = N35 and size = i3236) or
	  (m = N36 and size = i3237) or
	  (m = N37 and size = i3238) or
	  (m = N38 and size = i3239)
}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 TreeSetIntVar, exactly 39 TreeSetIntVarNode, 1 int, exactly 40 JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38) -> lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38) {
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
 +
 N22->N23
 +
 N23->N24
 +
 N24->N25
 +
 N25->N26
 +
 N26->N27
 +
 N27->N28
 +
 N28->N29
 +
 N29->N30
 +
 N30->N31
 +
 N31->N32
 +
 N32->N33
 +
 N33->N34
 +
 N34->N35
 +
 N35->N36
 +
 N36->N37
 +
 N37->N38
}


fun node_prevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38) {
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
   +
   N23->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22)
   +
   N24->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23)
   +
   N25->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24)
   +
   N26->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25)
   +
   N27->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26)
   +
   N28->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27)
   +
   N29->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28)
   +
   N30->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29)
   +
   N31->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30)
   +
   N32->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31)
   +
   N33->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32)
   +
   N34->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33)
   +
   N35->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34)
   +
   N36->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35)
   +
   N37->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36)
   +
   N38->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37)
 )
}


fun node_rprevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38) {
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
   +
   N23->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23)
   +
   N24->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24)
   +
   N25->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25)
   +
   N26->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26)
   +
   N27->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27)
   +
   N28->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28)
   +
   N29->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29)
   +
   N30->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30)
   +
   N31->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31)
   +
   N32->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32)
   +
   N33->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33)
   +
   N34->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34)
   +
   N35->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35)
   +
   N36->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36)
   +
   N37->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37)
   +
   N38->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
 )
}


fun node_relprevs[] : (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38) -> set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38) {
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
   +
   N23->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23)
   +
   N24->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24)
   +
   N25->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25)
   +
   N26->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26)
   +
   N27->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27)
   +
   N28->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28)
   +
   N29->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29)
   +
   N30->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30)
   +
   N31->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31)
   +
   N32->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32)
   +
   N33->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33)
   +
   N34->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34)
   +
   N35->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35)
   +
   N36->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36)
   +
   N37->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37)
   +
   N38->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
}


fun node_min[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38) {
 es - es.(
   N0->(N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N1->(N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N2->(N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N3->(N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N4->(N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N5->(N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N6->(N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N7->(N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N8->(N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N9->(N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N10->(N11+N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N11->(N12+N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N12->(N13+N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N13->(N14+N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N14->(N15+N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N15->(N16+N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N16->(N17+N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N17->(N18+N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N18->(N19+N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N19->(N20+N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N20->(N21+N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N21->(N22+N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N22->(N23+N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N23->(N24+N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N24->(N25+N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N25->(N26+N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N26->(N27+N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N27->(N28+N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N28->(N29+N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N29->(N30+N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N30->(N31+N32+N33+N34+N35+N36+N37+N38)
   +
   N31->(N32+N33+N34+N35+N36+N37+N38)
   +
   N32->(N33+N34+N35+N36+N37+N38)
   +
   N33->(N34+N35+N36+N37+N38)
   +
   N34->(N35+N36+N37+N38)
   +
   N35->(N36+N37+N38)
   +
   N36->(N37+N38)
   +
   N37->(N38)
 )
}




