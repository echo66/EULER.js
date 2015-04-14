/* module RDFEngine

* RDFEngine version of the engine that delivers a proof
* together with a solution
* Anti-looping mechanism and code for anti-looping mechanism is from Jos De Roo.

* data structures are:
* goallist = list of triples
* stack
* pathdata (a kind of inference history)
* graphs : the RDF graphs
* query
* state: string
* matchlist: list of found matches of the goal with the database
* These data are assembled in an object InfData called inf.
* Author: Guido J.M. Naudts Bouwel
*/

var currentGoal;

function solve(inf){         // inf are the infData
	/* unification of a goal with the database */
    inf.unSteps ++;""    // count the unification steps
    // lines for testing
    //print("inf.unSteps " + inf.unSteps + "\n");
    if (inf.maxSteps > 0 && inf.unSteps > inf.maxSteps){
          inf.state = "endinf";
          return;
    }

    if (inf.cached){
        inf.newTriples = concat(inf.newTriples,inf.cache);
        inf.cache=[];
    }

        if (inf.goallist.length == 0){
             // when the goallist is empty a solution has been found
            inf.state = "solution";
            inf.sols.push(inf.subst);
            return;
        }
        else if (inf.goallist[0] == null && inf.goallist.length == 1){    // null must be skipped
           inf.goallist= [];
           inf.state = "solution";
           // got to check dnot violation

           if (! inf.nobuiltins){
               checkContradictionsB();
           }
           inf.sols.push(inf.subst);
           return;
        }
        else if (inf.goallist[0] == null){
                inf.goallist.shift();
                solve(inf);
        }
        else{
            // apply current substitutions to the goal
           var g = inf.goallist[0];
            if (g.getProperty().getType() == "sr"  &&
                g.getProperty().uri == prefix){
                // skip prefix triples
                inf.goallist.shift();
                inf.state = "inf";
                return;
            }

           g = applySubstitutionListToTriple(inf.subst, g);
	       testVerbose(inf, "current goal: " + g.toString()+"\n");
           if (g.pending != 1){
                    //print("not pending!\n");
                    // now get all matches of the goal with the database
                    inf.matchlist = alts(g, inf);
                    //testVerbose(inf,"matched substitutions: " + inf.matchlist + "\n");
                    if(inf.matchlist.length == 0){  // the goal did not match
                        inf.state = "failure";
                        return;
                   }
                    currentGoal = g;
                    g.pending = true;
                    // now go and select one of the alternatives to continue the search
                    choose(inf);
            }else{
                    testVerbose(inf, " pending!\n");
                    if (testGrounded(g)){
                        // grounded means the goal does not contain variables
                        inf.cache.push(g);
                    }
                    inf.goallist.shift();
                    inf.state = "inf";

            }
        }
}

function choose (inf){
               /* choose one of the alternatives found with the function solve */
                  //print("choose matchlist " + inf.matchlist + "\n");
                  // get the data from the first alternative
                  var ms = inf.matchlist.shift();
                  if (ms.fromRule){
                     //writeln("ms[0]: " + ms[0] + " nr: " + ms[0].t1.nr)
                     currentGoal.fromRule = ms[0].t1.nr;
                     currentGoal.fromFact = 0;
                  }else{
                      //writeln("ms not fromrule: " + ms);
                      currentGoal.fromRule = 0;
                      currentGoal.fromFact = ms[0].t1.nr;
                  }
                  var subst1 = ms[0].subst;
                  var fs = ms[0].goals;
                  var t2 = ms[0].t2;
                  var t1 = ms[0].t1;
                  var lev = inf.level; // retrieve the current inferencing level
                  // make a copy of the goallist
                  var goallist = [];
                  for (var i = 0; i < inf.goallist.length; i++)
                       goallist[i] = copyTriple(inf.goallist[i]);
                   // save the other alternatives on the stack
                   if (inf.matchlist.length != 0 ) { /*&& (subst1.length != 0
                     || (subst1.length == 0 && t2.getType() == "r"))){   */
                    var substC = copySubstitutionList(inf.subst);
                    var elem = new stackElement(substC, goallist, inf.matchlist, lev);
                    inf.stack.unshift(elem);
                    }
                // add the new substitution
               // complex composition of substitutions
               //inf.subst = mergeSubstitutions([inf.subst, subst1])[0];
               // simple compositionof substitutions
               inf.subst = mergeSubstitutions1([inf.subst, subst1]);
                // prefix the goallist with the new goals
                if (! testNull(fs)){    // all the goals are not nil
                    for (var i = 0; i < fs.length; i++){
                        // change the inferencing level
                        tr = fs[i];
                        /* if (tr != null){
                           if (tr.fromRule > 0)
                               // this triple originates from a rule
                               renameTriple(tr, inf.level + 1, 0);
                       }*/
                   }
                   //if (inf.goallist.length > 0)
                   //      inf.goallist[0].pending = true;
                   for (var i = fs.length-1; i > -1; i--)
                       inf.goallist.unshift(fs[i]);
                }else
                   inf.goallist.shift();
                // save the new pathdata
                var pd = new pathDt(t2, t1, lev);
                inf.pathdata = [pd] + inf.pathdata;
                // augment the level
                inf.level += 1;
                // set the state to main
                inf.state = "inf";
                return;

}

function pathDt(t2, t1, lev){
   this.t2 = t2;
   this.t1 = t1;
   this.lev = lev;
}

function backtrack(inf){
	/* backtrack in search of a solution */
        //print("RDFEngine.backtrack stack length: " + inf.stack.length + "\n");
        testVerbose(inf, "RDFEngine.backtrack stack length: " + inf.stack.length + "\n");
        if (inf.stack.length == 0)
          inf.state = "endinf";
	else{
          // get data from the stack

          var elem = inf.stack.shift();
          var lev = elem.lev;
          inf.level = lev;
          // history data of failure paths is not kept;
          // take it away
          reducepd(inf.pathdata, lev);
          inf.goallist = elem.gs;
          currentGoal = inf.goallist[0];
          inf.subst = elem.subst;
          inf.matchlist = elem.ms;
          inf.state = "backtracked";
         }
}

function stackElement(subst, gs, ms, lev){
   this.subst = subst;
   this.gs = gs;
   this.ms = ms;
   this.lev = lev;
   this.toString = function(){
      var s = "StackElement:\n\n";
      s = s + "Subst: " + this.subst + "\n";
      s = s + "Goallist:\n" + this.gs + "\n";
      s = s + "Matchlist:\n" + this.ms + "\n";
      return s + "Level: " + this.lev + "\n**********************************\n";
   };
}

function reducepd(pd, lev){
    // destroy history data with level greater or equal to lev
    if (pd.length == 0)
        return;
    while (pd[0].lev >= lev){
        pd = pd.shift();
        if (pd.length == 0)
            return;
    }
}

function testNull(fs){
   // check whether all triples in a set are null
   for (var i = 0; i < fs.length; i++)
     if (fs[i] != null)
       return 0;
   return 1;
}

function alts(g, inf){

        // get all triples with the same property
        var pmatch = copyTripleset(getMatching(g, inf, "b"));
        //writeln("RDFEngine.alts matching: " + pmatch  + " goal= " + g + "\n") ;

        // keep track of the number of unifications
        inf.unifs += pmatch.length;
        // rename the variables with a higher level
        // print("inf.level " + inf.level + "\n");
        renameTripleSet(pmatch, inf.level + 1, 0);
        // print("pmatch = " + pmatch + "\n");
        // return the list of alternatives
        return matching(pmatch, g, inf);
}

function matching (ts, f, inf){
	/*  match a fact with the triple store
            ts is the triplestore (all triples with the same predicate); f is the fact.
	*/
        var list = [];
        var res;
        var t;
        for (var i = 0; i < ts.length; i++){
           t = ts[i];
           //print("matching unifyTriples f = " + f + " t = " + t);
           res = unifyTriples(f, t);

           if (res.length != 0){
               testVerbose(inf, "Matched triple: " + t + " nr: " + t.nr + "\n");
               //writeln("Matched triple: " + t + " nr: " + t.nr + "\n");
               if (t.getType() == "r"){
                   if (! hasBeenAppliedBefore(inf, t, f)){
                        res.fromRule = true;
                        list.push(res);
                   /*}else{
                       writeln("loooping!!!!");
                   } */
                   }
               }else{
                   if (! hasBeenAppliedBeforeF(inf, t, f)){
                        res.fromFact = true;
                        list.push(res);
                   /*}else{
                       writeln("loooping!!!!");
                   } */
                   }
               }
          }
        }
        //print("RDFEngine.getMatching list: " + list);
        return list;
}

    /** tests whether a goal has been matched with a rule before.
     * When it is, a looping in the inferencing process is detected.
     */
   function hasBeenAppliedBefore( inf, rule, goal ) {

      var entry;
      var num;
      //writeln("RDFEngine.hasBeenAppliedBefore rule: " + rule
      //        + " goal: " + goal);
      for( var i = 1; i < inf.goallist.length; i++ ) {
         entry = applySubstitutionListToTriple(inf.substitutionList, copyTriple(inf.goallist[i]));
         num = entry.fromRule;
          //writeln("RDFEngine.hasBeenAppliedBefore entry: " + entry + " num: " + num);
          //writeln("pending: " + entry.pending + " equivalent: " + isEquivalentGoal( entry, goal ));
          if(num != undefined && entry.pending && num > 0 && isEquivalentGoal( entry, goal )
               && num == rule.nr  ) {
            //writeln("Looping detected. Rule: " + rule + " goal: " + goal);
            testVerbose(inf, "Looping detected. Rule: " + rule + " goal: " + goal);
            return true;
         }

      }
      return false;
   }

/** tests whether a goal has been matched with a fact before.
 * When it is, a looping in the inferencing process is detected.
 * the goal may not be grounded
 */
   function hasBeenAppliedBeforeF( inf, fact, goal ) {

  var entry;
  var num;
  //writeln("RDFEngine.hasBeenAppliedBefore rule: " + rule
  //        + " goal: " + goal);
  if (testGrounded(goal)){
      return false;
  }
  for( var i = 1; i < inf.goallist.length; i++ ) {
     entry = applySubstitutionListToTriple(inf.substitutionList, copyTriple(inf.goallist[i]));
     num = entry.fromFact;
      //writeln("RDFEngine.hasBeenAppliedBefore entry: " + entry + " num: " + num);
      //writeln("pending: " + entry.pending + " equivalent: " + isEquivalentGoal( entry, goal ));
      if(num != undefined && entry.pending && num > 0 && isEquivalentGoal( entry, goal )
           && num == fact.nr  ) {
        //writeln("Looping detected. Rule: " + rule + " goal: " + goal);
        testVerbose(inf, "Looping detected. Rule: " + rule + " goal: " + goal);
        return true;
     }

  }
  return false;
   }


function renameTripleSet(ts, level, reset){
	/*  rename the variables in a tripleset
	     if reset undo the renaming
	*/
                 if (ts.length == 0 || ts == null)
                      return;
                  for (var i = 0; i < ts.length; i++)
                     renameTriple(ts[i], level, reset);
                  return;
}

function renameTriple(t, level, reset){
	/* rename the variables in a triple (level renumbering)
            if reset undo the renaming
	*/
        if (t == null){
           // alert("renameTriple: t == null");
           return;
        }
        if (t.getType() == "r"){
               renameTripleSet(t.getAntecedents(), level, reset);
               renameTripleSet(t.getConsequents(), level, reset);
               return;
        }
        //writeln("renameTriple triple: " + t  + " type = " + t.getType());
        renameAtom(t.getSubject(), level, reset);
        renameAtom(t.getProperty(), level, reset);
        renameAtom(t.getObject(),  level, reset);
        return;
}

function renameAtom(res, level, reset){
	/* rename a variable (level renumbering)
	    if reset undo the renaming
	*/
        //  for the moment there are only universal local variables
        //  renaming is only for local variables!!!
        if (! (res instanceof resource) && !(res instanceof cResource)){
            writeln("Res is not a resource!!!: " + res );
        }
        //writeln("res = " + res + " type: " + res.getType() + " uri: " + res.uri);
        if (res.RDFList != undefined && res.RDFList.length != 0)    // this atom is a list
           for (var i = 0; i < res.RDFList.length; i++)
               renameAtom(res.RDFList[i], level, reset);
        else if (res.getType() == "cr")  // this is a complex resource
           for (var i = 0; i < res.set.length; i++)
               renameTriple(res.set[i], level, reset);
        else if (res.uri.substring(0,2) == "_:")
           return;
        if (res.testVar()){      // this is a variable
           if (reset)
             res.level = 0;
	   else
              res.level = level;
        }
        return ;
}

function testGrounded(triple){
    var sub = triple.getSubject();
    if (sub != null && sub.testVar())
       return 0;
    var prop = triple.getProperty();
    if (prop != null && prop.testVar())
       return 0;
    var obj = triple.getObject();
    if (obj != null && obj.testVar())
       return 0;
    return 1;
}

function checkContradictionsB(inf){
     var tr;
     var uri;
     var temp = concat(inf.triples, inf.newTriples);
     for (var i = 0; i < temp.length; i++){
         tr = temp[i];
         uri = tr.getProperty().uri;
         //writeln("Backward.checkContradictionsB uri = " + uri + "\n");
         if (uri == dnot){
             ts = copyTripleset(tr.getObject().getSet());
             var ts1 = [];
             ts1 = copyTripleset( ts);
             // must now check for contradictions
             // attention! The query may not be treated as a builtin!!!
             // Set parameter nobuiltins !!!
             //writeln("Backward.checkContradictionsB ts1 = " + arrayToString(ts1) + "\n");

             sols1 = lightInf(temp, ts, inf, true);

             if ( sols1 != null && ! sols1.length == 0){
                 // contradiction discovered
                 //writeln("Backward.checkContradictionsB contradiction found!!" + arrayToString(ts1));
                 inf.abort = true;
                 inf.contradiction = arrayToString(ts1);
                 inf.state = "endInf";
                 return true;
             }

         }

     }
     return false;
}