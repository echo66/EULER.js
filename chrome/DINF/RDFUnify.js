/** Module defining substitutions and unfications for RDF backward resolution
  * Author: Guido Naudts. Bouwel
  */

// format of a substitution: (variable, resource)
function substi(vari, res){
   this.vari = vari;
   this.res = res;
   this.toString = function(){
     var a,b;
     if ( this.vari == undefined){
         a = "UNDEFINED";
     }else{
         a = vari.toString();
     }
     if ( this.res == undefined){
         b = "UNDEFINED";
     }else{
         b = res.toString();
     }

     return "(" +  a + ", " +
        b + ")";
   };
}

// attention: substitutions modify the input triples!!!!

function applySubstitutionListToDB(sl,db){
          /* apply a substitution to a RDF datasource*/
         var dbout = [];
         for (var i = 0; i < DB.length; i++)
              dbout.push(applySubstitutionListToTripleSet(sl, DB[i]));
          return dbout;
}  

function copySubstitutionList(substl){
   copyl = [];
   for (var i = 0; i < substl.length; i++)        
      copyl.push(substl[i]);
   return copyl;
}   

function substListToString(substl){
    var s = "";
    for (var i = 0; i < substl.length; i++)
        s = s + "[" + substl[i].toString() + "]";
    return s + "\n";
}

function applySubstitutionToTriple(subst, tripleIn){
        /*  apply a substitution to a triple */
    //writeln("RDFUnify.applySubstitutionToTriple tripleIn = " + tripleIn);

        try{
           tripleIn.setSubject(applySubstitutionToResource(subst, tripleIn.getSubject()));
           tripleIn.setProperty(applySubstitutionToResource(subst, tripleIn.getProperty()));
           tripleIn.setObject(applySubstitutionToResource(subst, tripleIn.getObject()));
        }catch(ex){
           print("RDFUnify.ApplysubstitutionToTriple exception: " + ex +
                 "\nTriple = " + arrayToString(tripleIn) + "\n");
        }
        return tripleIn;
}

function applySubstitutionListToTriple(sl, t){
        /* apply a substitutionlist to a triple */
        if (sl == null || sl.length == 0){
            return t;
        }
        if (t.getType() == "r"){  // this is a rule
           t.ants = applySubstitutionListToTripleSet(sl, t.getAntecedents());
           t.cons = applySubstitutionListToTripleSet(sl, t.getConsequents());
           return t;
        }
        for (var i = 0; i < sl.length; i++)
                t = applySubstitutionToTriple(sl[i], t);
        //writeln("RDFUnify.applySubstitutionListToTriple t = " + t);
        return t;
}

function applySubstitutionToTripleSet(subst, ts){
          /* apply a substitution to a tripleSet */
         // print("RDFUnify.applySubstitutionListToTripleSet ts = " + ts + "\n");
         //    print("RDFUnify.applySubstitutionListToTripleSet subst = " + subst + "\n");

          var out = [];
          for (var i = 0; i < ts.length; i++){
             //writeln("ts[i] " + arrayToString(ts[i]) + " " + ts[i].getType());
             out.push(applySubstitutionToTriple(subst,ts[i]));
          }
          return out;
}

function applySubstitutionListToTripleSet(sl, ts){
          /* apply a substitution to a tripleSet */
          //print("RDFUnify.applySubstitutionListToTripleSet ts = " + arrayToString(ts) + "\n");
          //print("RDFUnify.applySubstitutionListToTripleSet sl = " + sl + "\n");
          var out = [];
          for (var i = 0; i < ts.length; i++){

             out.push(applySubstitutionListToTriple(sl, ts[i]));
          }
          //writeln("RDFUnify.applySubstitutionListToTripleSet out = " + out);
          return out;
}

function applySubstitutionListToResource(sl, res){
          /* apply a list of subtitutions to a resource */
          var res;
          if (sl == undefined){
              print("sl is not defined;;;;");
              return res;
          }
          for (var i = 0; i < sl.length; i++)
                  res = applySubstitutionToResource(sl[i], res);
          return res;
}

function applySubstitutionListToResourceList(sl, resl){
          /* apply a list of subtitutions to a resource list */
          var out = [];
          for (var i = 0; i < resl.length; i++)
                  out.push(applySubstitutionListToResource(sl, resl[i]));
          return out;
}


function applySubstitutionToResource(subst, res){
          /* apply a substitution to a resource
             resource can be a number or a list of triples.
          */

          //writeln("RDFUnify.applySubstitutionToResource subst = " + subst.toString()
          //        + " $$$ " + res.toString() + "type = " + res.getType());
          var ret = res;
          if (subst.vari == undefined){
              ret = res;
          }

          else if (res == undefined)
              ret = res;
          else if (res.RDFList != undefined && res.RDFList.length != 0){
             var list = [];
             // print("subst = " + subst + "RDFList = " + res.RDFList + "\n");
             for(var i = 0; i < res.RDFList.length; i++)
               list.push(applySubstitutionToResource(subst, res.RDFList[i]));
             res.RDFList = list;
             ret = res;
          }
          else if (res.getType() == "cr"){
              //writeln("applySubstitutionToResource res = " + arrayToString(res.set));
              res.set = applySubstitutionToTripleSet(subst, res.set);
              ret = res;
          }
          else if (testEqualResources(subst.vari, res)){
              //print("subst.vari = " + subst.vari.toString() + " res = " + res.toString() + "\n");

              ret = subst.res;   // replace the resource by the substitution resource
          }
          //writeln("RDFUnify.applySubstitutionToResource ret = " + ret);
          return ret;
}

function unifyResources(r1, r2){
          /* Unification:
          unifyResource r1 r2 returns a list containing a single substitution s which is
          the most general unifier of terms r1 r2.  If no unifier
          exists, the list returned is empty.
          */
          //writeln("RDFUnify.unifyResources r1= " + r1 + " r2 = " + r2);
          if (r1.getType() == "cr")     // complex resource
              if (r2.getType() == "cr"){
                 // two triplesets must match triple by triple;
                 // otherwise a query builtin must be used
                 //writeln("RDFUnify.unifyResources r1= " + r1 + " r2 = " + r2);
                 var mli;
                 if ( r1.set.length != r2.set.length){
                     return [];
                 }
                 var sl = [];
                 for (var k = 0; k < r1.set.length; k++){
                    mli = unifyTriples( applySubstitutionListToTriple(sl, r1.set[k]),
                            applySubstitutionListToTriple(sl, r2.set[k]));
                    if (mli.length == 0){
                        return [];
                    }
                    //writeln("RDFUnify.unifyResources ml " + arrayToString(ml));
                    sl = concat(sl, mli[0].subst);
                    //writeln("RDFUnify.unifyResources sl = " + arrayToString(sl));

                 }
                 //writeln("RDFUnify.unifyResources mli " + arrayToString(sl));
                 // got to extract the substitutions
                 return sl;
              }else
                 return [];
          if (r2.getType() == "cr"){
                return [];
          }
          if (r1.getType() == "lr"){     // lists
              if (r2.getType() == "lr"){ // elements must match in sequence
                  if ( r1.RDFList.length != r2.RDFList.length){
                      return [];
                  }

                 var sl = [];
                 for(var i = 0; i < r1.RDFList.length; i++){
                     mli = unifyResources( applySubstitutionListToResource(sl, r1.RDFList[i]),
                            applySubstitutionListToResource(sl, r2.RDFList[i]));
                     //print("mli !!! " + mli);
                     if (mli.length == 0){
                         return [];
                     }
                     sl = concat(sl, mli);
                 }
                 return sl;
              }else{
                 return  [];
              }

          }
          if (r2.getType() == "lr"){
              return [];
          }

          if (r1.testVar())
                return [new substi(r1, r2)];
          if (r2.testVar())
                return [new substi(r2, r1)];
          if (r1.nr == r2.nr){
                // print("r1.nr = " + r1.nr + " r2.nr = " + r2.nr + "r2.res = " + r2.res + "\n");
                return [new substi(null, null)];
          }
          return [];
}

function unifyTriples(t1, t2){
          /* unify two triples; second can be a rule */
          //print("t1 ==== " + t1 + "\n");

          if (t1 == undefined || t2 == undefined){
          //    print("t2  ===== " + t2 + " t1: " + t1 + "\n");
              return [];
          }
          // with triplesets can return a a list of substitutionlists (more than one solution)
          if (t2.getType() == "r"){  // this is a rule
               var cons = t2.getConsequents();  // get the consequents
               var ants = t2.getAntecedents();  // get the antecedents
               var ruleNr = t2.nr;
               var un;
               var un4;
               var t;
               for (var i = 0; i < cons.length; i++){
                // need only unify with one consequent
                    t = cons[i];
                    t.fromRule = -ruleNr;
                    un = unifyTriples(t1, t);
                    //print("un = " + un + "\n");
                    if (un.length != 0){
                       var tr;
                       var ants1 = [];
                       var subst;
                       for (var i1 = 0; i1< ants.length; i1++){
                           tr = ants[i1];
                           tr.fromRule = ruleNr;
                           ants1.push(tr);
                       }
                       subst = un[0].subst;
                       return [new mlist(subst, ants1, t2, t1)];
                    }
               }
               return [];
          }
          else{
              var un1 = unifyResources(t1.getSubject(), t2.getSubject());
              var subst2;
              if (un1.length != 0){    // subjects unify
                   //print("subjects unify " + arrayToString(un1) + "\n");
                   var un2 = unifyResources(t1.getProperty(),
                                        applySubstitutionToResource(un1[0], t2.getProperty()));
                   if (un2.length != 0){   // properties unify
                        //print("properties unify " + un2 + "\n");
                        var un3 = unifyResources(t1.getObject(),
                                             applySubstitutionListToResource([un1[0] + un2[0]], t2.getObject()));
                        //print("RDFUnify.unifyTriples objects unify?. " + arrayToString(un3) + "\n");

                        if (un3.length != 0){   // objects unify
                            //print("RDFUnify.unifyTriples objects unify. " + arrayToString(un3) + "\n");
                            // un1, un2 and un3 are lists
                            // un4 = mergeSubstitutions1([un1, un2, un3]);
                            // print("merged1 " + substListToString(un4) + "\n");
                            un = mergeSubstitutions1([un1, un2, un3]);
                            //print("RDFUnify.unifyTriples merged " + arrayToString(un) + "\n");
                            // eliminate empty substitutions
                            subst2 = elimNone(un);
                            //print("RDFUnify.unifyTriples substl: " + arrayToString(subst2) + "\n");
                            // empty substitutions are produced by matching of two equal triples
                            if (t1.fromRule < 0)
                                return [new mlist(subst2, [], copyTriple(t2),copyTriple( t1))];
                            else
                                return [new mlist(subst2, [null], copyTriple(t2), copyTriple(t1))];
                        }
                        else
                            return [];
                   }
                   else
                        return [];
              }
              else
                   return []; // unification failed
           }
}

// format of a matchlist: (substitution, goals, triple1, triple2)
function mlist(subst, goals, t1, t2){
   this.subst = subst;
   this.goals = goals;
   this.t1 = t1;
   this.t2 = t2;
   this.toString = function(){
      var s = "\nSubst: " + this.subst + "\n" +
         "Goals: " + triplesetToString(this.goals) + "\nt1: " +
         this.t1.toString() + "\nt2: " + this.t2.toString() + "\n";
      return s;
   };
}

function elimNone(substlist){
    var sout = [];
    for (var i = 0; i < substlist.length; i++){
       var subst = substlist[i];
       if (subst.vari != undefined)
            sout.push(subst);
    }
    return sout;
}



function mergeSubstitutions(list){
  // merge a list of substitution lists
  // complex merge for efficiency
  var l = list.length;
  if (l == 0)
     return [];
  if (l == 1)
     return list;
  // compose the last two substitution lists ; replace the forelast
  // with the merge and eliminate the last.
  var su = composeSubstitution(list[l-2], list[l-1]);
  list[l-2] = su;
  list.pop();
  return mergeSubstitutions(list);
}

function composeSubstitution(substlist1, substlist2){
  // compose two substitutions
  if (substlist1 == [])
     return substlist2;
  if (substlist2 == [])
     return substlist1;
  var l1 = [];
  var l2 = [];
  for (var x = 0; x < substlist2.length; x++)
     l1.push(new substi(substlist2[x].vari,
        applySubstitutionListToResource(substlist1,
         substlist2[x].res)));
  l1 = cleanUp(l1);
  l2 = filter(substlist2, substlist1);
  return mergeSubstitutions1([l2, l1]);
}

function cleanUp(substlist){
   var out = [];
   var subst;
   for (var x = 0; x < substlist.length; x++){
      subst = substlist[x];
      if (subst.vari != null && subst.res != null)
          if (! testEqualResources(subst.vari, subst.res))
             out.push(subst);
      if (subst.vari == null && subst.res == null)
          out.push(subst);
   }
   return out;
}

function domain(substlist){
  // get the domain of a substitutionlist
  var out = [];
  if (substlist == [])
     return out;
  if (substlist == null)
     return out;
  for (var x = 0; x < substlist.length; x++)
     out.push(substlist[x].vari);
  return out;
}

function filter(substlist1, substlist2){
  // filter the domain of the first substitution list from the second
  var out = [];
  if (substlist1 == [])
     return out;
  if (substlist2 == [])
     return out;
  var dom = domain(substlist1);
  for (var x = 0; x < substlist2.length; x++){
     if (! elem(substlist2[x].vari, dom))
        out.push(substlist2[x]);
  }
  return out;
}

function elem(resource, list){
    if (list == [])
        return 0;
    for (var x = 0; x < list.length; x++){
        if (resource != null && list[x] != null)
           if (testEqualResources(resource, list[x]))
              return 1;
        else if (resource == null)
          return 0;
    }
    return 0;
}

function mergeSubstitutions1(list){
    // simple merge of substitutions for testing
    // and as a help function
    var out = [];
    var x2;
    for (var x = 0; x < list.length; x++){
       x2 = list[x];
       for (var x1 = 0; x1 < x2.length; x1++)
             out.push(x2[x1]);
    }
    return out;
}

function mergeSubstitutions2(list){
    // simple merge of substitutions for testing
    // and as a help function
    var out = [];
    var x2;
    for (var x = 0; x < list.length; x++){
       x2 = list[x];
       for (var x1 = 0; x1 < x2.length; x1++)
             out.push(x2[x1][0]);
    }
    return out;
}

function unifyNoRule(ts1, ts2){
    /* unify two triplesets that do not contain rules.
        len(ts1) < len(ts2)
        Returns all possible unifications.
        This is in fact a mini-inference engine;
        it can be used for a query in a tripleset not containing rules
        Returns a list = [[substitutionList, substituted]]
   */
   if (ts1.length == 0 || ts2.length == 0)
        return [];
   else
        return altsN(ts1, ts2);
}

function altsN(ts1, ts2){
     var q = copyTripleset(ts1);
     var q1;
     var as = sll(ts1, ts2);
     //print("\nRDFUnify.altsN as = " + as + "\n");
     //print("ts1.length = " + ts1.length +"\n");
     var ret = [];
     for (var i = 0; i < as.length; i++){
           q1 = copyTripleset(q);
           //print("as[i] = " + as[i] + "\n");
           ret.push([as[i],applySubstitutionListToTripleSet(as[i], q1)]);
     }
     //print("\nret = " + ret + "\n");
     return ret;
}

function sll(ts1, ts2){
       return solveN(ts1, ts2, [], []);
}

function unifyTripleWithTripleSet(triple, ts2){
       var ret = [];
       for(var i = 0; i < ts2.length; i++)
           //print("triple = " + triple + " ts2[i] = " + ts2[i] + "\n");
           
           ret.push(unifyTriples(triple, ts2[i]));
       return ret;
}

function solveN(ts1, ts2, stack, substList){
         //print("ts1.length  = " + ts1.length + "\n");
         if (ts1.length == 0){
             var ret = backtrackN(ts2, stack);
             ret.unshift(substList);
             return ret;
         }else{
             var triple;
             var alters = [];
             triple = applySubstitutionListToTriple(substList, ts1[0]);
             //print("RDFUnify.solveN goal N = " + triple + "\n" + " ts = " + arrayToString(ts2));
             alters = unifyTripleWithTripleSet(triple, ts2);
             //print("RDFUnify.solveN alters = " + alters + "\n");
             if (alters == [])
                 return chooseN([], subArray(ts1,1, ts1.length), ts2, stack, substList);
             else{
                     var slls = [];
                     var alts;
                     for(var i = 0; i < alters.length; i++){
                         try{
                           slls.push(alters[i][0].subst);
                         }catch(ex){}
                     }
                     //print("slls = " + slls + "\n");
                     return chooseN(slls, subArray(ts1,1, ts1.length), ts2, stack, substList);
               }
           }
} 

function chooseN(mli, ts1, ts2, stack, substList){
        if (mli.length == 0){
            //print("mli is null.\n");
            return backtrackN(ts2, stack);
        }
        else if (ts1.length == 0){
            //print("mli = " + mli[0] + "\n");
            stack.unshift([[], subArray(mli, 1, mli.length),
                          copySubstitutionList(substList)]);
            substList = concat(substList, mli[0]);
            //print("substList = " + substList + "\n"); 
            return solveN([], ts2, stack, substList);
         }else{
              //print("mli2 = " +mli[0] + "\n");
              stack.unshift( [copyTripleset(ts1), subArray(mli, 1, mli.length),
                 copySubstitutionList(substList)]);
              substList = concat(substList, mli[0]);
              return solveN(ts1, ts2, stack, substList);
         }
}

function backtrackN(ts1, stack){
        if (stack == null || stack.length == 0){
              //print("stackN =   " + stack + "\n"); 
              return [];
        }else{
            var ret;
            var ts;
            var sll;
            var mli;
            ret = stack[0];
            ts = ret[0];
            sll = ret[1];
            mli = ret[2];
            stack = subArray(stack, 1, stack.length);
            return chooseN(sll, ts, ts1, stack, mli);
        }
}

// format of a matchlist: (substitution, goals, triple1, triple2)
function copyml(mlA){
   var ret = [];
   for (var i=0; i < mlA.length; i++)
        ret.push(new mlist(mlA[i][0], mlA[i][1], mlA[i][2], mlA[i][3]));
   return ret;
}

            
//  Haskell: where -- alts = 
//         alts = [((applySubstitutionListToTripleSet ts1 a)
//                                 ,a)|a <- sll]
//         sll = solve ts1 ts2 [] []
//         solve []     ts2 stack substList
//                       -- = error ("notr " ++ show substList)
//            = substList:backtrack ts2 stack
//         solve (t:ts) ts2 stack substList
//            |alts == [] = choose [] ts ts2 stack substList
//            |otherwise = choose sll (ts) ts2 stack substList
//            where triple = applySubstitutionListToTriple t substList
//                  res = unifyTripleWithTripleSet triple ts2
//                  sll = [sls|(_, sls) <- alts] 
//                  (bool,alts) = res
//
//         choose []  ts ts2 stack substList = backtrack ts2 stack 
//                                         -- = error (show substList)
//         choose (sl:sll) [] ts2 stack substList
//            = solve [] ts2 stack1 substList1
//                                 --     = error ("no trips" ++ show substList)
//            where substList1 = substList ++ sl
//                  stack1 = ([], sll, substList):stack
//         choose (sl:sll) ts ts2 stack substList
//            = solve ts ts2 stack1 substList1
//            where substList1 = substList ++ sl
//                  stack1 = (ts, sll, substList):stack
//
//         backtrack ts2 [] = []  -- error "stack empty"
//         backtrack ts2 ((ts,sll, sl):st) 
//            = choose sll ts ts2 st sl
//                
 
