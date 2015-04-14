/**
  * module for checking and distributing builtins 
  * should be split into several modules later ?? maybe
  * Author: Guido J.M. Naudts Bouwel
  */


var notEqualTo = "http://www.w3.org/2000/10/swap/log#notEqualTo";
var conclusion = "http://www.w3.org/2000/10/swap/log#conclusion";
var semantics = "http://www.w3.org/2000/10/swap/log#semantics";
var variables = "proctest#variables";
var implies = "http://www.w3.org/2000/10/swap/log#implies";
var js = "http://eulermoz/builtins#js";   // javascript
var jsp = "http://eulermoz/builtins#jsp"; // javascript program
var not = "http://eulermoz/builtins#not"; // FOL negation
var pnot = "http://eulermoz/builtins#pnot"; // prefixed not
var dnot =  "http://eulermoz/builtins#dnot"; // declarative not
var program = "http://eulermoz/builtins#program";
var proc = "proctest#proc";
var query = "proctest#query";
var call = "proctest#call";
var mult = "http://www.w3.org/2000/10/swap/math#product";
var logsum = "http://www.w3.org/2000/10/swap/math#sum";
var greater = "http://www.w3.org/2000/10/swap/math#greaterThan";
var equal = "http://www.w3.org/2000/10/swap/math#equalTo";
var prefix = "prefix:abbrev";
var builtinList =
        // logic builtins
        [conclusion, semantics, not, pnot, notEqualTo,
        // programming builtins
        call, js, jsp,
        // math builtins
        mult, logsum, greater, equal
        ];

function checkBuiltins(inf, triple1){
                //print("checkBuiltins entry triple1: " + triple1);
                var uri = triple1.getProperty().uri;
                switch(uri){
                    case js:
                        // handle javascript instructions
                        // format : [em:js (?x,"javascript_instructions")].
                        // substitutable variables in the javascript should be
                        // appended with a question mark for parsing.
                        // eg. ?x em:js "var x = 2. ?y?**?z?/2".
                        // where ?y and ?z are N3 variables that must be substituted.
                        // em:js = http://eulermoz/builtins#js
                        // Second format:
                        // ?x em:jsp "program_label".
                        // program_label refers to:
                        // "program_label" em:program "javascript program".
                        // this has as purpose not to clutter up the rules.
                        var obj = triple1.getObject();
                        var subj = triple1.getSubject();

                        if (! subj.testVar || obj.getType() != "lt") {
                            inf.state = "failure";
                            testVerbose(inf, "Javascript builtin failure: " +
                                             triple1.toString() + "\nFormat: ?variable <http://eulermoz/builtins#js> " +
                                             "  \"javascript instructions\".\n");
                            return 1;
                        }
                        var jslit = substituteVariables(obj.toString(), inf);
                        if (jslit == null) {
                            inf.state = "failure";
                            testVerbose(inf, "Javascript builtin failure: error in variables " +
                                             triple1.toString() + "\nFormat: ?variable <http://eulermoz/builtins#js> " +
                                             "  \"javascript instructions\".\n");

                            return 1;

                        }
                        var result = new resource(eval(jslit).toString());
                        result.constant = 1;
                        var subst = new substi(subj, result);
                        inf.goallist.shift();
                        // save the new pathdata
                        inf.pathdata = [new pathDt(triple1, triple1, inf.level)] + inf.pathdata;
                        testVerbose(inf, "builtin matched: " + triple1.toString());
                        inf.subst.push(subst);
                        break;
                    case jsp:
                        // see uri == js.
                        var obj = triple1.getObject();
                        var subj = triple1.getSubject();

                        if (! subj.testVar || obj.getType() != "lt"){
                            inf.state = "failure";
                            testVerbose(inf, "Javascript builtin failure: " +
                                    triple1.toString() + "\nFormat: ?variable <http://eulermoz/builtins#js> " +
                                    "  \"javascript instructions\".\n");
                            return 1;
                        }

                        // got to find the triple: obj em:program "program".
                        var triple = new cTriple(obj, new resource(program), new resource("?program"));
                        print("graphs  = " + inf.graphs);
                        var triples = getMatchingR([inf.triples], triple, inf);
                        // should be only one
                        triple = triples[0];
                        if (triple == null){
                            inf.state = "failure";
                            testVerbose(inf, "Javascript builtin failure: error in javascript module: " +
                                    triple1.toString() + "\nThe program does not exist!!.\n");

                            return 1;

                        }

                        var jslit  = substituteVariables(triple.getObject().toString(), inf);
                        if (jslit == null){
                            inf.state = "failure";
                            testVerbose(inf, "Javascript builtin failure: error in variables " +
                                    triple1.toString() + "\nFormat: ?variable <http://eulermoz/builtins#js> " +
                                    "  \"javascript instructions\".\n");

                            return 1;

                        }
                        var result = new resource(eval(jslit).toString());
                        result.constant = 1;
                        var subst = new substi(subj, result);
                        inf.goallist.shift();
                        inf.pathdata = [new pathDt(triple1, triple1, inf.level)] + inf.pathdata;
                        testVerbose(inf, "builtin matched: " + triple1.toString());
                        inf.subst.push(subst);
                        break;
                    /*case dnot:
                        // a check is done 1)if a declaration exists
                        //                 2)for a contradiction
                        // as contradictions can arise in a later phase,
                        // we have to store the negation triple.
                        // we store it in inf.dnotTriples.
                        // ! we first search matching declarations
                        print("inf.triples;;;;; " + inf.triples);

                        var sols = lightInf(inf.triples, [triple1], inf);

                        print("sols:: " + sols);
                        var ts;
                        if (sols == null || sols.length == 0){
                            inf.state="failure";   // no declaration available
                            return 1;
                        }else{
                            // each solution gives different alternatives
                            var matches = [];
                            for (sol in sols){
                                ts = applySubstitutionListToTripleSet(
                                        sol, copyTripleSet(triple1.getObject));
                                inf.dnot.push = ts;
                                elimDoubleTriplesets(inf.dnot);
                                writeln("Triple cheeeeck: " + checkTripleset(ts));
                                // must now check for contradictions
                                writeln("tssssssss " + arrayToString(ts) + "\n");
                                // attention! The query may not be treated as a builtin!!!
                                // Set parameter nobuiltins !!!
                                sols1 = lightInf(inf.triples, ts, inf);

                                if ( sols1 != null && ! sols1.length == 0){
                                    // contradiction discovered
                                    inf.abort = true;
                                    inf.state = "endInf";
                                    return 1;
                                }else{
                                    // must push the alternative
                                    matches.push(sol);
                                }

                            }
                            print("matches aare : " + matches);
                            inf.goallist.shift();
                            inf.matchList = matches;
                            chooseR(inf);
                            inf.builtin=true;

                            return 0;
                        }
                        // contradictions will be searched for elsewhere also
                        // (in function addTriplesNewTriples in Forward.js)

                        break;*/
                    case notEqualTo:    // handle log:notEqualTo
                       var sub = triple1.getSubject();
                       var obj = triple1.getObject();
                       if (sub.uri != obj.uri) { // the condition is fulfilled
                          inf.goallist.shift();
                          // save the new pathdata
                          inf.pathdata = [new pathDt(triple1, triple1, inf.level)] + inf.pathdata;
                          testVerbose(inf, "builtin matched: " + triple1.toString());
                       }else{ // failure!!
                           testVerbose(inf, "builtin failure: " + triple1.toString());
                           inf.state = "failure";
                           return 1;
                       }
                       break;
                     case semantics:
                        // :subject log:semantics ?g means :subject is a .n3 file and ?g is the name of the parsed db
                        var filename = triple1.getSubject().uri;
                        // now fetch this file
                        break;

                     case call:
                         // call a procedure; the subject is the procedure name
                         // the object is the parameter list
                         // get the name
                         // print("call entry substitutions are = " + inf.subst + "\n");
                         print("builtins triple1 = " + triple1 + "\n");
                         var procName = triple1.getSubject().uri;
                         try{
                            // get the procedure
                            var procparams = inf.proclist[procName];
                         }catch(e){alert("This procedure has not been declared: " + procName + "\n")}
                         var procvariables = procparams[0];
                         var tripleset = copyTripleset(procparams[1]);
                         var t, set1, set2, list = [];
                         for (var i = 0; i < tripleset.length; i++){
                            //print("tripleset[i] " + tripleset[i].getType() + "\n");
                            t = tripleset[i];
                            // transform these triples to rules
                            if (t.getProperty().uri == implies) {
                               set1 = t.getSubject().set;
                               set2 = t.getObject().set;
                               list.push(new rule(set1, set2));
                            }
                         }
                         tripleset = list;
                         // print("******************************************************\n");
                         // print("procedure body = " + tripleset + "\n");
                         var query = copyTripleset(procparams[2]);
                         // make the substitutions
                         var variablesIn = triple1.getObject().RDFList;
                         // print("RDFList triple1.object = " + variablesIn + "\n");
                         // match variablesIn with procvariables
                         var substList = [];
                         if (variablesIn.length != procvariables.length)
                            alert("Not matching number of variables! procname = " +
                                   procName + "\n VariablesIn: " +
                                    variablesIn + " \n " +  " proc variables: " + procvariables + "\n");
                         for (var i = 0; i < variablesIn.length; i++)
                             substList.push(new substi(procvariables[i], variablesIn[i]));
                         // print("The substList is " + substList + "\n");

                         // initialize the (sub)inferencing
                         var db1 = new db(tripleset);
                         var db2 = new db(query);
                         db1.makePropertyDict();
                         db2.makePropertyDict();
                         var inf1 = new infData([db1, db2]);
                         inf1.verbose = inf.verbose;
                         // copy the procedures for recurrent calls
                         inf1.initinf();
                         // do a chcek for queryvariables
                         checkForQueryVariables(db2.ts);
                         // make a list of all variables on input
                         var varsIn = [];
                         for (var i = 0; i < variablesIn.length; i++){
                             if (variablesIn[i].testVar())
                                varsIn.push(variablesIn[i]);
                         }
                         // apply the substitutionlist to all triples
                         db1.ts = applySubstitutionListToTripleSet(substList, db1.ts);
                         db2.ts = applySubstitutionListToTripleSet(substList, db2.ts);
                         // print("call db1 = " + db1 + " db2 " + db2 + "\n");
                         // pointer to proclist for recurrent calls
                         inf1.proclist = inf.proclist;
                         // no output
                         inf1.nooutput = 1;
                         // do the reasoning
                         inference(inf1);
                         // get the solutions
                         var sols = inf1.sols;
                         // print("builtin sols: " + sols + "\n");
                         // print("varsIn are " + varsIn + "\n");
                         // apply this susbtitution to the variables
                         var results = [];
                         // create the variable substitutions
                         var varsInOld = [];
                         for (var i = 0; i < varsIn.length; i++)
                            varsInOld[i] = varsIn[i];
                         for (var i = 0; i < sols.length; i++)
                            results.push(applySubstitutionListToResourceList(sols[i], varsIn));
                         var substOut = [];
                         for (var i = 0; i < results.length; i ++){
                             var substO = [];
                             for (var i1 = 0; i1 < results[i].length; i1++)
                                 substO.push(new substi(varsInOld[i1], results[i][i1]));
                             substOut.push(substO);
                         }
                         inf.subst = concat(inf.subst, substOut[0]);
                         inf.goallist.shift();
                         // print("inf.subst = " + inf.subst + "\n");
                         var elem = new stackElement(subArray(substOut, 1, substOut.length), inf.goallist, inf.matchlist, inf.lev);
                         inf.stack.unshift(elem);

                          // save the new pathdata
                          inf.pathdata = [new pathDt(triple1, triple1, inf.level)] + inf.pathdata;
                          testVerbose(inf, "builtin matched: " + triple1.toString());
                          testVerbose(inf, "results of call are " + substOut + "\n");
                          break;
                    case mult:    // handle math:mult
                       var factors = triple1.getSubject().RDFList;
                       // make the product
                       var prod = 1;
                       for (var i = 0; i < factors.length; i++){
                          // print("factors[i] = " + factors[i] + "\n");
                          prod = prod * factors[i];
                       }
                       var res = new resource(prod.toString());
                       res.constant = 1;
                       var subst = new substi(triple1.getObject(), res);
                       inf.goallist.shift();
                       // save the new pathdata
                       inf.pathdata = [new pathDt(triple1, triple1, inf.level)] + inf.pathdata;
                       testVerbose(inf, "builtin matched: " + triple1.toString());
                       // print("mult subst = " +subst + "\n");
                       inf.subst.push(subst);
                       break;
                    case logsum:    // handle math:sum

                       var factors = triple1.getSubject().RDFList;
                       // print("sum factors are: " + factors + "\n");
                       // make the product
                       var sum = 0;
                       for (var i = 0; i < factors.length; i++)
                          sum = sum + factors[i]*1;
                       var res = new resource(sum.toString());
                       res.constant = 1;
                       var subst = new substi(triple1.getObject(), res);
                       inf.goallist.shift();
                       // save the new pathdata
                       inf.pathdata = [new pathDt(triple1, triple1, inf.level)] + inf.pathdata;
                       testVerbose(inf, "builtin matched: " + triple1.toString());
                       inf.subst.push(subst);
                       break;
                    case greater:    // subject is greater than object
                       var sub = parseFloat(triple1.getSubject().uri.toString());
                       var obj = parseFloat(triple1.getObject().uri.toString());
                       //print("sub = " + sub + " obj = " + obj);
                       // save the new pathdata
                       inf.pathdata = [new pathDt(triple1, triple1, inf.level)] + inf.pathdata;

                       if (sub > obj){
                          testVerbose(inf, "builtin matched: " + triple1.toString());
                          inf.goallist.shift();
                       }else{
                           testVerbose(inf, "builtin failed: " + triple1.toString());
                           inf.goallist.shift();
                           inf.state = "failure";
                           return 1;
                       }
                       break;
                    case equal:    // subject is equal to object
                       var sub = parseFloat(triple1.getSubject().uri.toString());
                       var obj = parseFLoat(triple1.getObject().uri.toString());
                       // save the new pathdata
                       inf.pathdata = [new pathDt(triple1, triple1, inf.level)] + inf.pathdata;

                       if (sub == obj){
                          inf.goallist.shift();
                          testVerbose(inf, "builtin matched: " + triple1.toString());
                       }else{
                          inf.goallist.shift();
                          inf.state = "failure";
                          testVerbose(inf, "builtin failed: " + triple1.toString());                           
                          return 1;
                       }
                      break;

                    default:
                        inf.builtin = false;
                        return 0;

                }


               /*  else{
                     inf.builtin = false;
                     return 0;
                 }*/
                 if (inf.goallist.length == 0){  // a solution has been reached
                    inf.sols.push(inf.subst);
                    inf.state = "solution";
                 }else
                    inf.state = "inf";

                 return 0;
}


function checkForQueryVariables(set){
    // check whether in a procedure query all variables are
    // marked as variable
    var t;
    for (var i = 0; i < set.length; i++){
       t = set[i];
       testResourceForQueryVariables(t.getSubject());
       testResourceForQueryVariables(t.getProperty());
       testResourceForQueryVariables(t.getObject());
    }
}

function testResourceForQueryVariables(res){
    var uri = res.uri;
    if (uri == undefined ){
        return

    }
    if (uri.length > 4 && ( uri.substring(0,5) == ":G$$$"
         || (uri.substring(0,5) == ":T$$$" && res.cr == true)
         || uri.substring(0,5) == ":E$$$" ))
         if (res.nr > 0)
            res.nr = -res.nr;
    //print("testResourceForQueryVariables res.nr = " + res.nr + " res = " + res + " res.cr= " + res.cr +  "\n");
    var vt;
    try{
       vt = res.varType;
       if (vt == "gel" || vt == "ge" || vt == "gul" || vt == "gu")
          if (res.nr > 0)
             res.nr = -res.nr;
    }catch(e){}
}

function substituteVariables(lit, inf){
    var i, i1, i2;
    var vars = [];
    var s;
    var res;
    i2 = 0;
    i = 0;
    i = lit.indexOf("?");
    while ( i >=0 ){
       i1 = lit.indexOf("?", i+1);
       if ( i1 < 0){
           // throw exception
           testVerbose( inf, "Bad variables:  " + lit + "\n" +
                   "The variables must be enclosed with \"?\"\n");
           return null;
       }
       s = lit.substring(i, i1 );
       res = new resource(s);
        // we got to substitue the variables and replace them in the string
        // with their substituted value; if variables are not substituted there
        // is an error.
       print("substitutions !!! " + inf.subst + " res== " + res + "\n");
       vars[s] = applySubstitutionListToResource( inf.subst, res);
       print("vars[s] = " + vars[s] + "\n");
       if (vars[s].getType() != "lt" ){
           testVerbose( inf, "N3 variables in javascript must be substituted to literals: \n" +
                   lit + "\n");
           return null;
       }
       i2++;
       i = lit.indexOf("?", i1 + 1)
    }
    for (var s in vars){
       var done = false;

       while (!done){
           i = lit.indexOf(s + "?");
           if (i < 0){
               done = true;
           }else{
               lit = lit.substring(0,i) + vars[s] + lit.substring(i + s.length + 1);
           }
       }


    }

    return lit;
}
