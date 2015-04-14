/* module  Forward.js
 * This module is a forward reasoning engine.
 * Rules are contained in inf.rules
 * Author: Guido J.M. Naudts Bouwel
 */

function reason(inf){
   inf.newFound = 1;
   inf.newTriples = [];
   inf.newTemps = [];
   inf.unSteps = 0;
   //inf.verbose = true;
   var graph;
   var triple;
   var rule;
   //inf.nooutput = false;
   inf.maxSteps = -1;


   if (inf.rules == undefined || inf.rules == []){    // get all rules now
          inf.rules = [];
          for (var i1 = 0; i1 < inf.graphs.length; i1++){
             graph = inf.graphs[i1].ts;
             for (var i2 = 0; i2 < graph.length; i2 ++){
                  triple = graph[i2];
                  if (triple.getType() == "r")
                       inf.rules.push(triple);
             }
         }
    }

   if (inf.triples == undefined || inf.triples == []){    // get all triples now
          inf.triples = [];
          for (var i1 = 0; i1 < inf.graphs.length; i1++){
             graph = inf.graphs[i1].ts;
             for (var i2 = 0; i2 < graph.length; i2 ++){
                  triple = graph[i2];
                  if (triple.getType() != "r")
                       inf.triples.push(triple);
             }
         }
    }
   // make dictionary
   makePropertyDictI(inf);
   //writeln("PropertyDictM: " + propertyDictMToString(inf));
   //writeln("Forward.reason triples from propertyDictM: " + getAllTriplesM(inf));
   // print("lengths " + inf.rules.length + " " + inf.triples.length + "\n");
   // main loop; loop till no new triples are found or one solution is found
  var nt = 0; // keeps track of new triples
  var  time1 = myClock();
  var time2;
  while (inf.newFound){
      inf.newFound = 0;
      testVerbose(inf, "\n$$$$$$$$$ apply all rules $$$$$$$$$$\n");
      for (var i1 = 0; i1 < inf.rules.length; i1++){
           if (inf.abort){
               break;
           }
           rule =  inf.rules[i1];
           testVerbose(inf, "rule = " + rule + "\n");
           //writeln("Forward.reason rule = " + rule + "\n");
           inf.goallist = copyTripleset(rule.ants);
           //print("inf.goallists before loop " + inf.goallist + "\n");
           inf.state = "inf";
           inf.subst = [];
           if (inf.dnotActive){
               checkContradictions(inf);
           }
           while (inf.state != "endInf"  ){
               inf.unSteps++;
               if (inf.maxSteps > 0 && inf.unSteps > inf.maxSteps){
                     inf.state = "endinf";
                     return;
               }

                 testVerbose(inf, "inf.state = " + inf.state + "\n");
                 if (inf.state == "next"){
                      var cons1 = applySubstitutionListToTripleSet(inf.subst, copyTripleset(rule.cons));
                      testVerbose(inf, "substitutions: " + inf.subst + "\n");
                      addTriplesNewTriples(inf, cons1);
                      if (! inf.abort){
                          testVerbose(inf, "New triples found: " +
                                        triplesetToString(cons1));
                          //writeln("New triples found: " + triplesetToString(cons1));

                          //writeln("state next inf.newFound = " + inf.newFound + "\n");
                          backtrackR(inf);
                      }
                 }
                else  if (inf.state == "failure"){
                    // this was a dead path; backtrack and try agan
                    testVerbose(inf, "Failure path done.\n");
                    backtrackR(inf);
                }
               else if (inf.state == "backtracked"){
                    // a backtrack was done
                    testVerbose(inf, "A backtrack has been done.\n");
                    // print("matchlist after backtrack: " +inf.matchlist);
                    //  go and choose new goals
                   chooseR(inf);
                }else{
                   var ret;
//                   if (inf.goallist.length != 0){
                          testVerbose(inf, "Goallist:\n" + triplesetToString(inf.goallist) + "\n");
                          // display the current substitution
                          testVerbose(inf, "Current Substitutions:\n"
                             + inf.subst + "\n");
                          solveR(inf);
//                    }
                }

           }
           testVerbose(inf, "End of reasoning for this rule.\n");
          //  inf.newTriples.concatR(inf.newTriples, inf.newTemps);
       }
       if (inf.abort){
           break;
       }
       testVerbose(inf,  "New triples : " + inf.newTriples + "\n");
       //print("inf.newFound = " + inf.newFound + "\n");
   }
   //writeln("PropertyDictM: " + propertyDictMToString(inf));
   testNooutput(inf, "\nEnd --- new triples: " + inf.newTriples.length + "\n");
   testNooutput(inf, "Inferencing steps: " + inf.unSteps + "\n");
   // now get the solutions
   // sols is an array of triplesets
   // each tripleset is a solution
   var sols = elimDoubleTriplesets(getSolutions(inf));
   inf.solbuf = sols;
   var s = "\nSolutions:\n\n";
   if (sols.length == 0)
       s = s + "There were no solutions found.\n";
   if(inf.abort){
        s = s + "Reasoning was aborted because a contradiction happened:\n" +
            inf.contradiction + "\n";
   }else{
       for (var i = 0; i < sols.length; i++){
 //          s = s + triplesetToString(sols[i]) + "\n";
       }
   }
   time2 =  myClock();
   testNooutput(inf, "Starting time FW : "  + time1 + "\n");
   testNooutput(inf, "Ending time FW : "  + time2 + "\n");
   testNooutput(inf, s + "\n");
}

function getSolutions(inf){
    // copy the query
    //print("inf.query " + inf.query);
    checkForQueryVariables(inf.query);
    var q = [];
       for (var i = 0; i < inf.query.length; i++)
          q.push(copyTriple(inf.query[i]));
    // get all triples
    var triples = concat(inf.triples, inf.newTriples);

    //print("q = " + q + " triples = " + triples + "\n");
    var solss = lightInf( triples, q, inf, true);
    // the solutions
    //print("inf.query " + inf.query);

    var sols = [];
    for (var i = 0; i < solss.length; i++)
       sols.push(convertSol(applySubstitutionListToTripleSet(solss[i],copyTripleset(inf.query))));
    return sols;
}

function convertSol(solution){
    if ( ! (solution instanceof Array)) {
        return solution;
    }
    var t;
    var out = [];
    for (var i=0; i < solution.length; i++){
        t = solution[i];
        if (t.getProperty().getUri() != prefixPredicate.getUri()){
            out.push(t);
        }
    }
    return out;
}


function lightInf(tripleset, query, inf, nobuiltins){
   // a lightweight sub-inferencing process
   // returns the solution as an array of substitutions
   // initialize the inferencing
   // Attention: entry 1 and entry 2 must be arrays!!!
   // if nobuiltins is true then no builtns will be used in the inferencing
   if (inf.verbose)
       writeln("Forward.lightInf QUERY  " + arrayToString(query)  + "\n");
   //writeln("Forward.lightInf QUERY  " + arrayToString(query)  + "\n");
   if (query == undefined || query.length == 0){
       return [];
   }
   var db1 = new db(tripleset);
   var db2 = new db(query);
   db1.makePropertyDict();
   db2.makePropertyDict();

   var inf1 = new infData([db1, db2]);
   if ( inf != undefined)
       inf1.verbose = inf.verbose;
   inf1.nodict = true;
   inf1.initinf();
   inf1.matchingMechanism = inf.matchingMechanism;
   makePropertyDictI(inf1);
   // do a check for queryvariables
   //writeln("Forward.reason triples from propertyDictM: " + getAllTriplesM(inf1));

   checkForQueryVariables(db2.ts);

   //writeln("Forward.lightInf db1 = " + db1 + " db2 " + db2 + "\n");
   // pointer to proclist for calls
    if ( inf != undefined){
        inf1.proclist = inf.proclist;
        inf1.nooutput = inf.nooutput;
    }
    // do the reasoning
    //writeln("inf1.goallist:: " + inf1.goallist);
    //writeln("inf1.stack " + arrayToString(inf1.stack) + "\n");

    inf1.nobuiltins = nobuiltins;

    inference(inf1);
    //print("Forward.lightInf  query = " + query);
    //if (inf.verbose)
     //writeln("Forward.lightInf inf1.sols = " + inf1.sols);
    // get the solutions
    return inf1.sols;
}


function solveR(inf){
        // inf are the infData
        /* unification of a goal with the database */
        //print("entering solve.\n");
        //print("inf.goallist = " + inf.goallist + "\n");
        //print("inf.unSteps = " + inf.unSteps + "\n");
    inf.unSteps++;
    if (inf.maxSteps > 0 && inf.unSteps > inf.maxSteps){
          inf.state = "endinf";
          return;
    }

        if (inf.goallist.length == 0){
             // when the goallist is empty new triples have been added
            inf.state = "next";
            return;
        }
        else if (inf.goallist[0] == null && inf.goallist.length == 1){    // null must be skipped
           inf.goallist= [];
           inf.state = "next";
           return;
        }
        else if (inf.goallist[0] == null){
                inf.goallist.shift();
                solve(inf);
        }
        else{

           var g = inf.goallist[0];
           if (g.getProperty().getType() == "sr"  &&
               g.getProperty().uri == prefix){
               // skip prefix triples
               inf.goallist.shift();
               inf.state = "inf";
               return;
           }
           g = applySubstitutionListToTriple(inf.subst, copyTriple(g));
           inf.goal = g;
           inf.builtin = true;
            // check whether the next predicate is a builtin
           //print("Forward.solveR g" + g);
           var ret = checkBuiltins(inf, g);
           //print("ret === " + ret);
           if (ret == 1){
               inf.state = "failure";
               return;
           }
           testVerbose(inf, "current goal: " + g.toString()+"\n");
            if ( inf.builtin == true){
                inf.state = "inf";
                return;
            }
            inf.goallist.shift();
            if ( inf.dnotActive){
            // for a declarative negation we have to check for contradictions
                var contradiction = checkDnot(inf, g);
                if ( contradiction ){
                    // processing aborted
                    return;
                }
            }
            // now get all matches of the goal with the database
            inf.matchlist = altsR(g, inf);
            //print("inf.matchlist : " + inf.matchlist + "\n");
            inf.unSteps += 1;    // count the unification steps
            // lines for testing
            // print("inf.unSteps " + inf.unSteps + "\n");
            if (inf.maxSteps > 0 && inf.unSteps > inf.maxSteps){
                 inf.state = "endinf";
                 return;
             }
             // now go and select one of the alternatives to continue the search
             chooseR(inf);
        }
}

function chooseR (inf){
                   /* lines for testing */
                    inf.unSteps++;
                    if (inf.maxSteps > 0 && inf.unSteps > inf.maxSteps){
                          inf.state = "endinf";
                          return;
                    }

               /* choose one of the alternatives found with the function solve */
              //
               if(inf.matchlist.length == 0){  // the goal did not match
                      inf.state = "failure";
                      return;
               }
               else{
                  //print("chooseR matchlist " + inf.matchlist + "\n");
                  // get the data from the first alternative
                  var ms = inf.matchlist.shift();
                  var subst1 = ms[0];
                  var lev = inf.level; // retrieve the current inferencing level
                  // make a copy of the goallist
                  var goallist = [];
                  for (var i = 0; i < inf.goallist.length; i++)
                       goallist[i] = copyTriple(inf.goallist[i]);
                   // save the other alternatives on the stack
                   if (inf.matchlist.length != 0){
                        var substC = copySubstitutionList(inf.subst);
                        var elem = new stackElementR(substC, goallist, inf.matchlist, lev);
                        inf.stack.unshift(elem);
                    }
                // add the new substitution
               // complex composition of substitutions
               //inf.subst = mergeSubstitutions([inf.subst, subst1])[0];
               // simple composition of substitutions
               inf.subst = mergeSubstitutions1([inf.subst, subst1]);
               // add the triple to newTemps
               // add only if the triple is not in newTemps or newTriples
               // set the state to main
                inf.state = "inf";

                addTripleNewTemps(inf);
                return;
          }
}


function backtrackR(inf){
	/* backtrack in search of a solution */
        //print("backtrackR stack.length = " +  inf.stack.length +"\n");
    inf.unSteps++;
    if (inf.maxSteps > 0 && inf.unSteps > inf.maxSteps){
          inf.state = "endinf";
          return;
    }

        if (inf.stack.length == 0){
          inf.state = "endInf";
          return;
        }else{
          // get data from the stack
          var elem = inf.stack.shift();
          inf.level = elem.lev;
          inf.goallist = elem.gs;
          inf.subst = elem.subst;
          inf.matchlist = elem.ms;
          inf.state = "backtracked";
          inf.newTemps = [];
          return;
         }
}

function stackElementR(subst, gs, ms, lev){
   this.subst = subst;
   this.gs = gs;
   this.ms = ms;
   this.lev = lev;
   this.toString = function(){
      var s = "Stack:\n\n";
      s = s + "Subst: " + this.subst + "\n";
      s = s + "Goallist:\n" + this.gs + "\n";
      s = s + "Matchlist:\n" + this.ms + "\n";
      return s + "Level: " + this.lev + "\n";
   };
}

function addTripleNewTemps(inf){
    // add a triple to newTemps only if not already in
   // in newTemps or newTriples
   var g =  applySubstitutionListToTriple(inf.subst, inf.goal);
   if (tripleInList(g, inf.newTemps) == 0 &&
        tripleInList(g, inf.newTriples) == 0)
        inf.newTemps.push(g);
}

function addTriplesNewTriples(inf, triples){
    // add a triple to newTriples if not already in it
   //print("addTriplesNewTriples triples = " + triples + "\n");
   //print("addTriplesNewTriples inf.newTriples = " + inf.newTriples + "\n");
   for (var i = 0; i < triples.length; i++){
       if (tripleInList(triples[i], inf.newTriples) == 0){
//            print("triples[i]  " + inf.newTriples +"   " + triples[i] +  "\n ");
//            print("   " + testEqualTriples(inf.newTriples, triples[i]) + "\n");
            inf.newTriples.push(triples[i]);
            inf.newFound = 1;
            addTripleToPropertyDict(triples[i], inf);
       }
   }

}


function altsR(g, inf){
       /*  get the alternatives, the substitutions and the backwards rule applications.
            getMatching gets a copy of all the triples with the same property or
            a variable property.
            ts is the set of graphs
            n is the level
            g is the goal
        */
        var ts = inf.triples;  // ts is a list of triples no rules
        // get all triples with the same property
        var pmatch = getMatching( g, inf, "f");
        //print("Forward.altsR pmatch = " + pmatch + "\n");
        // keep track of the number of unifications
        inf.unifs += pmatch.length;
        // return the list of alternatives
        return unifyNoRule([g], pmatch);
}




function getPropertyExtensionR(prop, ts){
       var t;
       var list = [];
       for (var i = 0; i <  ts.length; i++){
          t = ts[i];
          if (t.getType() != "r"){
             prop1 = t.getProperty();

             if (prop1.uri == prop.uri)
                list.push(t);
          }
       }
       return list;
}

/**
  * If a goal is a dnot builtin, the object triples must be added to inf.dnotTriples
  * also a check must be done whether they exist in the db.
  * if they do, there is a contradiction, then true is returned, otherwise false.
  */
function checkDnot(inf, goalIn){
    var uri = goalIn.getProperty().uri;
    if (uri != dnot){
        return false;
    }

    if ( goalIn.getObject().getType() != "cr" ){
        throwException("Invalid dnot builtin: " + goalIn);
    }

    var sols = lightInf(concat(inf.triples, inf.newTriples), [goalIn], inf, true);


    //print("Forward.checkDnot sols:: " + arrayToString(sols));
    var ts;
    if (sols == null || sols.length == 0){
        //nothing must be done; the normal reasoning process will
        // see the lack of declaration.
        return false;
    }else{
        // each solution gives different alternatives
        var sol;
        for (var i = 0; i < sols.length; i++){
            sol = sols[i];
            testVerbose(inf, "Forward.checkDnot sol = " + arrayToString(sol));
            ts = applySubstitutionListToTripleSet(
                    sol, copyTripleset(goalIn.getObject().getSet()));
            var ts1 = [];
            ts1 = copyTripleset( ts);
            // must now check for contradictions
            // attention! The query may not be treated as a builtin!!!
            // Set parameter nobuiltins !!!
            sols1 = lightInf(inf.triples, ts, inf, true);
            //writeln("Forward.checkDnot ts1 = " + arrayToString(ts1) + "\n");

            if ( sols1 != null && ! sols1.length == 0){
                // contradiction discovered
                testVerbose(inf,"Forward.checkDnot contradiction found!!" + arrayToString(ts1));
                inf.abort = true;
                inf.contradiction = arrayToString(ts1);
                inf.state = "endInf";
                return true;
            }

        }
       }
        return false;

}

function checkContradictions(inf){

     var tr;
     var uri;
     for (var i = 0; i < inf.triples.length; i++){
         tr = inf.triples[i];
         uri = tr.getProperty().uri;
         //testVerbose(inf, "Forward.checkContradictions uri = " + uri + "\n");
         if (uri == dnot){
             ts = copyTripleset(tr.getObject().getSet());
             var ts1 = [];
             ts1 = copyTripleset( ts);
             // must now check for contradictions
             // attention! The query may not be treated as a builtin!!!
             // Set parameter nobuiltins !!!
             sols1 = lightInf(inf.triples, ts, inf, true);
             //writeln("Forward.checkDnot ts1 = " + arrayToString(ts1) + "\n");

             if ( sols1 != null && ! sols1.length == 0){
                 // contradiction discovered
                 testVerbose(inf, "Forward.checkDnot contradiction found!!" + arrayToString(ts1));
                 inf.abort = true;
                 inf.contradiction = arrayToString(ts1);
                 inf.state = "endInf";
                 return true;
             }

         }

     }
     return false;


}