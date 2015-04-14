function N3EParser(){
   /**  This object is a notation3 parser.
     * Author: Guido J.M. Naudts Bouwel
     */
//      # get the proxy
//      # proxy with authentication: put the proxy address and port in
//      # "proxy.txt" and the userid and password (userid:password) in
//      # the file "userPass.txt"
//      # for proxy without authentication  put "noAuth"
//      # in the file "proxy.txt" and put the address and port number of
//      # the proxy in the environment variable "http-proxy".
//      # both files should exist.
//      # if no proxy is required, leave the files empty.
//      pr = PVa.PersistentString("proxy.txt")
//      proxy = pr.get()
//      # get the proxy userid and password
//      pr1 = PVa.PersistentString("userPass.txt")
//      userPass = pr1.get()
//      # proxy flag 0 = proxy with authentication; 1 = no proxy;
//      # 2 = proxy without authentication
//      authProxy = 0
//      # the internet access object
//      http = N3Http.N3Http()
    // ************* known uri's ******************
    this.rdf = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
    this.rdfs = "http://www.w3.org/2000/01/rdf-schema#";
    this.daml = "http://www.daml.org/2001/03/daml+oil#";
    this.log = "http://www.w3.org/2000/10/swap/log#";
    // ************* --------------- **************

    // tripleset containing the parsed triples
    this.tripleset = [];

    // counter for creating anonymous subjects
    this.anonCounter = 0;

    // parameter for length error output
    this.errLength = 50;

    // dictionary containing prefixes
    this.prefixDictionary = [];
    this.prefixDictionary["dc:"] = "dc:";
//    this.prefixDictionary[":"] = ":";

    // resource dictionary
    this.resdic = [];


    // flag indicating whether a query or not is parsed
    //this.queryFlag = 0;

    // flag indicating whether embedded triples have to be discarded
    // when full_generation = 1, only "simple" resources are generated i.e. with the list
    // attribute = []. E.g. :a :b {:s :p :o} becomes : :a :b :s. :s :p :o.
    // This parameter will generate different results in the inference engine.

    this.full_generation = 0;

    // flag indicating whether there was an error in parsing
    this.errorFlag = 0;

    // list with errors and comment
    this.errorList = [];

    // filename of parsed file
    this.fileName = "";

    // flag for handling "is .... of" construct
    this.inverseFlag = 0;

    // counter for giving a unique id to lists
    this.listCounter = 0;

    this.init = function(){
        //            if proxy == " " or proxy == "":
        //                 authProxy = 1
        //            elif proxy == "noAuth":
        //                 authProxy = 2
        // reset the tripleset
        this.tripleset = [];
        // dictionary of resources; index is a resource full label
        // content is a list [nr, resource]
        this.resdic = [];
        //            the list of origins.
        //            the position in the list is added to each triple
        //            this.originList = []
        //            detection of: " .. is .. of ... "
        //      
        // a counter for assigning  anonymous subjects
        this.anonCounter = 0;
        // a counter for tranforming local variables into global variables
        //this.locCounter = 0;
        // a counter for instantiating existential variables
        //this.existCounter = 0;
        // a debug flag
        // this.debug = 1
        // flag for directing the output
        // this.saveOnDisk = 0
        // the name of the file that is being parsed
        this.fileName = "";
        // a counter for assigning  anonymous subjects
        this.anonCounter = 1;
        // a counter for tranforming local variables into global variables
        //this.locCounter = 1;
        // a counter for instantiating existential variables
        //this.existCounter = 1;
        this.full_generation = 0;
        // counter for lists
        this.listCounter = 1;
        // counter for rules
        //this.ruleNr = 1;
        // reset queryflag
        //this.queryFlag = 0;   
        // empty errorlist
        this.errorList = []; 
        // reset the errorflag
        this.errorFlag = 0; 
        // utility functions
    }

    this.readN3 = function(path, fileName){
        this.n3String = readAFile(path, fileName);
    }

    this.genFull = function(){
        /* this generates extra triples so that only 'simple' resources rest.
         * (for a simple resource the attribute 'list' = []
         */
        var out = [];
        var t;
        var t1;
        var h;
        for (var i = 0; i < this.tripleset.length; i++){
           t = this.tripleset[i];
           if (t.subject.simple == 0)
            for (var i1 = 0; i1 < t.subject.set; i1++){
                t1 = t.subject.set[i1];
                out.push(t1);
                h = copyTriple(t);
                h.subject = t1.object;
                out.push(h);
            }
          else if (t.object.simple == 0)
            for (var i1 = 0; i1 < t.object.set; i1++){
                t1 = t.object.set[i];
                h = copyTriple(t);
                out.push(t1);
                h.object = t1.subject;
                out.push(h);
            }
          else
            out.append(t);
        }
        this.tripleset = out;
    }
            

    this.writeOutput1 = function(){
        // write output for the gui procedure
        print("ERRORFILE " +
            "\n=========================\n\n");
        for (var i = 0; i < this.errorList.length; i++)
            print(this.errorList[i] + "\n");
    }

    this.parseAFile = function(path, fileName){               
//            if (utils.startsWith(fileName,"http://") == "T"):
//               this.readUrl(fileName)
//            else:   
            this.readN3(path, fileName);
            //writeln("N3String = " + this.n3String );
            bool = this.parseN3(this.n3String);
            return bool;
    }

//
//   # read from an url
//   # output is in this.n3String
//      def readUrl(self, url):
//            if this.authProxy == 1 or this.authProxy == 2:
//               this.http.readUrl(url)
//               this.n3String = this.http.urldata
//            else:
//               this.http.proxyUrl(this.proxy, this.userPass, url)
//               this.n3String = this.http.urldata
//

// List of testcases
//# 0 allValuesFrom.n3             OK
//# 1 ontAx.n3(www.w3.org)$? syntax error?
//# 2 animal-result.n3 $           OK
//# 3 animal-simple.n3 $           OK
//# 4 animal.n3                    OK
//# 5 authen.axiom.n3              OK
//# 6 authen.lemma.n3              OK
//# 7 authen.proof.n3 $            OK
//# 8 danb-query.n3 $              OK
//# 9 danb-result.n3 $             OK
//# 10 danb.n3                     OK
//# 11 danc-query.n3 $             OK
//# 12 danc-result.n3 $            OK
//# 13 danc.n3 $                   OK
//# 14 etc.n3 $                    OK
//# 15 gedcom-facts.n3 $           OK
//# 16 gedcom-proof.n3 $           OK
//# 17 gedcom-query.n3 $           OK
//# 18 gedcom-relations-result.n3 $OK
//# 19 gedcom-relations-test.n3 $  OK
//# 20 gedcom-relations.n3 $       OK
//# 21 graph.axiom.n3 $            OK
//# 22 graph.lemma.n3 $            OK
//# 23 graph.proof.n3 $            OK
//# 24 janet-result.n3 $           OK
//# 25 janet-test.n3 $             OK
//# 26 janet.n3 $                  OK
//# 27 lists-query.n3 $            OK
//# 28 lists-result.n3 $           OK
//# 29 lists.n3 $                  OK
//# 30 vogel.q.n3 $                OK
//# 31 rdf-facts.n3 $              OK
//# 32 rdf-query.n3 $              OK
//# 33 rdf-result.n3 $             OK
//# 34 rdf-rules.n3 $              OK
//# 35 rdfc25May-result.n3 $       OK
//# 36 rdfc25May-test.n3 $         OK
//# 37 rdfc25May.n3 $              OK
//# 38 rdfs-query.n3 $             OK
//# 39 rdfs-result.n3 $            OK
//# 40 rdfs-rules.n3 $             OK
//# 41 russell.axiom.n3 $          OK
//# 42 russell.lemma.n3 $          OK
//# 43 russell.proof.n3 $          OK
//# 44 subclass-query.n3 $         OK
//# 45 subclass-result.n3 $        OK
//# 46 subclass.n3 $               OK
//# 47 subprop-query.n3 $          OK
//# 48 subprop-result.n3 $         OK
//# 49 subprop.n3 $                OK
//# 50 test-result.n3 # $          OK
//# 51 test-test.n3 $              OK
//# 52 test.n3 $                   OK
//# 53 tpoint-all.n3   $           OK
//# 54 tpoint-facts.n3 $           OK
//# 55 tpoint-query.n3 $           OK
//# 56 tpoint-result.n3 $          OK
//# 57 tpoint.n3 $                 OK
//# 58 varprop-query.n3 $          OK
//# 59 varprop-result.n3 $         OK
//# 60 varprop.n3 $                OK
//# 61 ziv-query.n3 $              OK
//# 62 ziv-result.n3 $             OK
//# 63 ziv.n3 $                    OK
//# 64 wol-facts.n3 $              OK
//# 65 wol-query.n3 $              OK
//# 66 wol-rules.n3 $              OK
//# 67 VOGEL.N3                    OK
//# 68 vogel.l.n3                  OK
//# 69 boole.lemma.n3              OK
//# 70 boole.axiom.n3              OK
//# 71 induction.axiom.n3          OK
//# 72 induction.query.n3          OK
//# 73 allValuesFrom.n3            OK
//# 74 Owls.n3                     OK

  this.parseN3 = function(s){
    /** prepare the parsing: split the input string into single lines.
      * a line is either comment or finishes with a dot.
      * prefix declarations are done before the use of the prefix!!!
      * all lines are copied into the errorlist
      * @todo parse long comment (between """ and """ ).
      */
   //writeln("parser parseN3 s = " + s);
   this.errorFlag = 0;
   if (s == ""){
      this.errorList.push("The input file is empty!!!");
      return 0;
   }else{
      var line;
      var p;
      var ret;
      var bool;
      var rest;
      var l1;
      var l2;
      var t;
      var tl;
      var ts;

      s = skipBlancs1(s);

      while (s.length > 0){
          s = skipBlancs1(s);
          line = "";
          if (s.length == 0)
               break;
          if (s[0] == "#"){   // comment
             p = this.parseComment(s.substring(1, s.length));
             //print("p = " + p + "\n");
             if (p == undefined || p.length == 0){
                this.errorFlag = 1;
                ret = this.synchronize(s);
                bool = ret[0];
                line = ret[1];
                s = ret[2];
                if (bool == 0){
                    this.errorList.push("Parsed = " + line);
                    return 0;
                }else
                    this.errorList.push("!!!error parsing comment!!!"
                         + line + "!!!!END");
             }else{
                line = p[0];
                s = p[1];
                this.errorList.push("#" + line + "\n");
             }
          }else if (s.substring(0,3) == "\"\"\""){
              // now we got to parse a long comment
              p = this.parseLongComment(s.substring(3, s.length));
              //print("p = " + p + "\n");
              if (p == undefined || p.length == 0){
                 this.errorFlag = 1;
                 ret = this.synchronize(s);
                 bool = ret[0];
                 line = ret[1];
                 s = ret[2];
                 if (bool == 0){
                     this.errorList.push("Parsed = " + line);
                     return 0;
                 }else
                     this.errorList.push("!!!error parsing long comment!!!"
                          + line + "!!!!END");
              }else{
                 line = p[0];
                 s = p[1];
                 this.errorList.push("\"\"\"" + line + "\"\"\"\n");
              }

          }else{  //  parse parameter or prefix or triple
             if (s.substring(0, 6) == "@param"){
                // format: @param name value.
                p = this.parseParam(s);
                if (p == undefined || p.length == 0){
                    this.errorFlag = 1;
                    ret = this.synchronize(s);
                    bool = ret[0];
                    line = ret[1];
                    s = ret[2];
                    if (bool == 0){
                        this.errorList.push("Parsed = " + line);
                        return 0;
                    }else{
                        this.errorList.push("/@/!!!error!!! parsing param!!!. Line: "
                                  + line + "/@/END\n");
                    }
                }else{
                    rest = p[1];
                    l1 = s.length;
                    l2 = rest.length;
                    l1 = l1 - l2;
                    line = s.substring(0, l1);
                    s = rest;
                    t = p[1];
                    this.tripleset.push(t);
                    this.errorList.push(line);
                }
             }else if (s[0] == "@"){
                    // writeln("parser parse prefix.");
                    p = this.parsePrefix(s);
                    if (p == undefined || p.length == 0){
                        this.errorFlag = 1;
                        ret = this.synchronize(s);
                        bool = ret[0];
                        line = ret[1];
                        s = ret[2];
                        if (bool == 0){
                            this.errorList.push("Parsed = " + line);
                            return 0;
                        }else{
                            this.errorList.push("/@/!!!error!!! parsing prefix!!!. Line: "
                                + line + "/@/END\n");
                        }
                    }else{
                        rest = p[1];
                        l1 = s.length;
                        l2 = rest.length;
                        l1 = l1 - l2;
                        line = s.substring(0, l1);
                        s = rest;
                        t = p[0];
                        this.tripleset.push(t);
                        this.errorList.push(line);
                    }
              }else{  // parse a triple
                    tl = this.parseTriple(s);
                    var se = checkTripleset(tl);
                    if (se != undefined){
                        writeln("Triples parsed: " + this.tripleset );
                        writeln("Type error in triple: " + se + "\n");
                        break;
                    }
                    if (tl == undefined || tl.length == 0){
                        this.errorFlag = 1;
                        ret = this.synchronize(s);
                        bool = ret[0];
                        line = ret[1];
                        s = ret[2];
                        if (bool == 0){
                            this.errorList.push("Parsed = " + line);
                            return 0;
                        }else
                            this.errorList.push("/@/!!!error!!! parsing triple!!!. Line: "
                                      + line + "/@/END\n");
                     }else{
                         ts = tl[0];
                         rest = tl[1];
                         for (var i = 0; i < ts.length; i++)
                             this.tripleset.push(ts[i]);
                         l1 = s.length;
                         l2 = rest.length;
                         l1 = l1 - l2;
                         line = s.substring(0, l1);
                         this.errorList.push(line + ".");
                         rest = skipBlancs(rest);
                         // skip dot
                         if (rest[0] == ".")
                             s = rest.substring(1, rest.length);
                         else
                             s = rest;
                     }

              }
          }
      }
      //writeln("Parser tripleset: " + this.tripleset);
      s = skipBlancs1(s);
      if (this.full_generation)
          this.genFull();
      if ( globalPrefixes != undefined){
          for (prefix in this.prefixDictionary){
              // double definitions are ignored;
              // the last one entered is in the dictionary!!
              globalPrefixes[this.prefixDictionary[prefix]] = prefix;
          }
      }
      return 1;
   }
  }


 // synchronize: parse the input string till the first dot
 this.synchronize = function(s){
   // parse s till the first dot
   this.errorFlag = 1;
   var ret = parseUntilString(s,".");
   var bool = ret[0];
   var parsed = ret[1];
   var rest = ret[2];
   this.errorList.push("SYNCHRONIZING !!!!!!!!!!!!!!");
   if (bool == 0){
      this.errorList.push("!!! MAJOR ERROR -- MISSING POINT NO SYNCHRONIZATION POSSIBLE");
      this.errorList.push("PARSING ABORTED!!!");
      return [0, s, ""];
   }else
      return [1, parsed + ".", skipBlancs1(rest.substring(1, rest.length))];
  }

  this.synchronize1 = function(s, ch){
   // parse s till char is met
   var ret;
   var bool;
   var parsed;
   var rest;
   ret = parseUntilString(s, ch);
   // print("synchronize1 ret = " + ret + "\n");
   bool = ret[0];
   parsed = ret[1];
   rest = ret[2];
   if (bool == 0)
     return [0, s, ""];
   else
     return [1, parsed + ch, skipBlancs1(rest.substring(1, rest.length))];
  }

  this.parseComment = function(s){
   /* function for parsing comment.
    * input is the string to be parsed.
    * the comment goes till "\r" or "\n" is encountered.
    * returns the comment and the rest string
    */
    var ret;
    var bool;
    var comment;
    var rest;
    if (s.length == 0)
       return ["", ""];
    else{
       ret = parseUntil("\n", s);
       bool = ret[0];
       comment = ret[1];
       rest = ret[2];
       if (bool)
          return [comment, skipBlancs1(rest)];
       else{
          ret = parseUntil("\r", s);
          bool = ret[0];
          comment = ret[1];
          rest = ret[2];
          if (bool)
             return [comment, skipBlancs1(rest)];
          else
             return [];
       }
    }
  }

  this.testParseComment = function(){
   this.parseN3("# blabla\n gaga");
   this.writeOutput1();
//            this.errorlist = []
//            this.parseN3("# blabla gaga. tata.")
   this.errorList = [];
   this.parseN3("# blabla gaga tata");
   this.writeOutput1();
  }

    this.parseLongComment = function(s){
     /* function for parsing a long comment.
      * input is the string to be parsed.
      * the comment goes till "\"\"\""  is encountered.
      * returns the comment and the rest string
      */

      var ret;
      var bool;
      var comment;
      var rest;
      if (s.length == 0)
         return ["", ""];
      else{
         ret = parseUntilString(s, "\"\"\"");
         bool = ret[0];
         if (bool){
            comment = ret[1];
            rest = ret[2];
            return [comment, skipBlancs1(rest.substring(3))];
         }
         else{
            return [];
         }
      }
    }

    this.testParseLongComment = function(){
        s = "@prefix : <http:test#>.\n" +
            "\"\"\" blabla\n gaga bla\n eee\"\"\":a :b\n:c. :e :f (:g :k :l).";
        print("Input: " + s + "\n");
        this.parseN3(s);
        this.writeOutput1();
        print(this.tripleset);
    }

 this.parsePrefix = function(s){
   /* function for parsing prefixes.
    * input is the string to be parsed.
    * returns a triple and the rest string
    * format of a prefix :
    * @prefix ...: <URI>
    * the prefix is added in the global prefix dictionary as
    * ("prefix","value-of-prefix")"""
    */
    if (s == "")
      return [];
    else{
      var sd;
      var bool1;
      var rest1;
      var prefix;
      var rest2;
      var bool2;
      var bool3;
      var rest3;
      var bool4;
      var uri;
      var rest4;
      var bool5;
      var rest5;
      sd = skipBlancs(s);
      ret = parseString("@prefix", sd);
      // print("ret = " + ret + " " + sd + "\n");
      bool1 = ret[0];
      rest1 = ret[1];
      ret = parseUntil(":", skipBlancs1(rest1));
      bool2 = ret[0];
      prefix = ret[1];
      rest2 = ret[2];
      ret = takec("<", skipBlancs1(rest2));
      bool3 = ret[0];
      rest3 = ret[1];
      ret = parseUntil(">", skipBlancs1(rest3));
      bool4 = ret[0];
      uri = ret[1];
      rest4 = ret[2];
      ret = takec(".", skipBlancs1(rest4));
      bool5 = ret[0];
      rest5 = ret[1];
      if (bool1 && bool2 && bool3 && bool4 && bool5){
         this.prefixDictionary[prefix + ":"] = uri;
         var triple;
         var subject;
         var property;
         var object;
         var re;
         var bool;
         ret = this.createRes("prefix:" + prefix);
         bool = ret[0];
         re = ret[1];
         if (bool == 0)  // resource does not exist
             this.res(re, "prefix:" + prefix,"prefix:","prefix:" + prefix);
         subject = re;
         ret = this.createRes("prefix:abbrev");
         bool = ret[0];
         re = ret[1];
         if (bool == 0)
              this.res(re, "prefix:abbrev", "prefix:" , "prefix:abbrev");
         property = re;
         ret = this.createRes(uri);
         bool = ret[0];
         re = ret[1];
         if (bool == 0)
              this.res(re, uri,"","<" + uri + ">");
         object = re;
         triple = new cTriple(subject, property, object);
         return [triple, rest5];
      }else  // an error has happened
         return [];
    }
}

  this.parseScript = function(s){

  }

  this.testParsePrefix = function(){
   /*   this.parseN3("@prefix  blabla\n gaga");
   this.writeOutput1();
   this.errorList = [];
   this.parseN3("@prefix c: http:# blabla gaga. tata.");
   this.writeOutput1();
   */
   this.errorList = [];
   this.parseN3("@prefix c: <http>.# blabla gaga tata.\n");
   this.writeOutput1();
  }

  this.testParseTriple = function(){
   var p;
   var tl;
   var rest;
   print("testParseTriple:\n");
/*   p = this.parseTriple(":s :p [:a :b],[:c :d], [:e :f].");
   if (p == [])
       print("failure parsing: " + ":s :p [:a :b],[:c :d], [:e :f].\n");
   else{
       print("parsing: " + ":s :p [:a :b],[:c :d], [:e :f].\n");
       tl = p[0];
       rest = p[1];
       print("triple = \n" + tl + "\nrest = " + rest + "\n");
   }


   p = this.parseTriple(":a :b :c.");
   if (p == [])
      print("failure parsing: " + ":a :b :c.\n");
   else{
      print("parsing: " + ":a :b :c.\n");
      tl = p[0];
      rest = p[1];
      print("triple = \n" + tl + "\nrest = " + rest + "\n");
   }
   p = this.parseTriple ("{:a :b :c. :d :e :f.} :g :h.");
   print("parsing: {:a :b :c. :d :e :f.} :g :h.\n");
   tl = p[0];
   rest = p[1];
   print("triple = \n" + tl + "\nrest = " + rest + "\n");
*/
   p = this.parseTriple ("[:b :c;[:d :e; :m :n] :r] :g :h.");
   if (p.length == [])
      print("failure parsing: " + "[:b :c;[:d :e; :m :n] :r] :g :h.\n");
   else{
      print("parsing: " + "[:b :c;[:d :e; :m :n] :r] :g :h.\n");
      tl = p[0];
      rest = p[1];
      print ("triple = \n" + tl + "\nrest = " + rest + "\n");
   }
   p = this.parseTriple ("{:person :member :institution. " +
                    ":institution :w3cmember <http://www.w3.org>. " +
                    ":institution :subscribed :mailinglist} :implies" +
                    "{:person :authenticated :mailinglist}. ");
   print ("parsing: " +
         "{:person :member :institution. " +
         ":institution :w3cmember <http://www.w3.org>. " +
         ":institution :subscribed :mailinglist} log:implies" +
         "{:person :authenticated :mailinglist}. \n")
   tl = p[0];
   rest = p[1];
   print("triple = \n" + tl + "\nrest = " + rest + "\n");
  }

  // test the function parseTripleSet.
  this.testParseTripleSet = function(){
   print("\ntestParseTripleSet\n******************");
/*   print("{:a :b :c.} " + this.parseTripleSet([], "{:a :b :c.}"));
   print("{{:a :b :c. :d :d :f} :g {:h :i :j. :k :l :m}} $$$ " +
         this.parseTripleSet([], "{{:a :b :c. :d :d :f} :g" +
         " {:h :i :j. :k :l :m}}"));
*/
   print("{{:a :b :c} :d :e} $$$ " + this.parseTripleSet([], "{{:a :b :c} :d :e}"));
//            print (( "", "{:a :b :c}", 0),this.parseTripleSet( "", "{:a :b :c}", 0))
//            print (("", "{:a :b :c. :d :e :f.}", 0), this.parseTripleSet("", "{:a :b :c. :d :e :f.}", 0))
//            print (("", "{:: :b :c. :d :e :f.", 0), this.parseTripleSet("", "{:: :b :c. :d :e :f.", 0))
//            print (("", ":a :b :c.", 0), this.parseTripleSet("", ":a :b :c.", 0))
//            print (("", "{:a is :b of :c.}.", 0), this.parseTripleSet("", ":a is :b of :c.}", 0))
//            print (("", "{:d :e :f. :a has :b of :c.}", 0), this.parseTripleSet("", ":d :e :f.:a has :b of :c.}", 0))
//            print (("", ":a :b :c", 0), this.parseTripleSet("", ":a :b :c", 0))
  }

  // parse a set of triples.
  // Returns a tripleset and a reststring
  this.parseTripleSet = function(ts, s){
   var sd;
   var first;
   var tr;
   var t;
   var rest;
   sd = skipBlancs(s);
   if (sd == "")
      return [ts, s];
   else{
      first = sd.substring(0, 1);
      // begin of set detected; check for end of set and call recursively
      if (first == "{"){
         tr = this.parseTriple(skipBlancs(sd.substring(1, sd.length)));
         if (tr.length == 0){
            this.errorList.push("!!!failure parsing triple!!! Line: " + s.substring(0,this.errLength));
            return [];
         }else{
            t = tr[0];
            rest = tr[1];
            ts = concat(ts, t); //ts.push(t);
            return this.parseTripleSet(ts, rest);
         }
       // "}" found - return.
       }else if (first == "}")
            return [ts, sd.substring(1, sd.length)];
       // must be the next triple : parseSubject and call parsePropertyList.
       else if (first == "."){
            sd = skipBlancs(sd.substring(1, sd.length));
            if (sd == "")
               return [ts,sd];
            if (sd.substring(0, 1) == "}")
               return [ts, sd.substring(1, sd.length)]
            else
               tr = this.parseTriple(sd);
            if (tr.length == 0){
               this.errorList.push("!!!failure parsing triple!!! Line: " + s.substring(0, this.errLength));
               return [];
            }
            else{
               t = tr[0];
               rest = tr[1];
               ts = concat(ts, t); //ts.push(t);
               return this.parseTripleSet(ts, rest);
            }
        }else{
            this.errorList.push("!!! error parsing tripleset - missing . or { or } !!!\n Line: " +
                           s.substring(0, this.errLength));
            return [];
        }
    }
  }


  this.parseTriple = function(s){
    /* parseTriple parses a singel triple.
     * returns a set of triples!!! and a reststring
     * if inverse flag subject and object are interchanged.
     */
     var sd;
     var first;
     var p;
     inverseFlag = 0;
     sd = skipBlancs(s);
     if (sd == "")
        return [];
     else{
        //writeln("before parseSuject()");
        p = this.parseSubject(sd);
        //writeln("after parseSubject() " + p);

        if (p == undefined || p.length == 0){
           this.errorList.push ("!!!error on parsing subject!!!\n" +
                  "synchronizing is done on dot. Line: " +                   s.substring(0,this.errLength));
           return [];
        }else{
           var sub = p[0];
           var rest = p[1];
           rest = skipBlancs(rest);
           var c = rest.substring(0, 1);
           if (c == "}" || c == "]" || c == ".")
              if (sub.set.length == 0)
                 return [];
              else
                 return [sub.set, rest];
           /* transferred to interface.js
           if (sub.label != undefined &&
                 sub.label.substring(0, 3) == ":T$$$" && queryFlag == 1
                 && sub.nr > 0)
              sub.nr = -sub.nr;*/
           var p1 = this.parsePropertyList([], rest);
           //print("parseTriple pl = " + pl + "\n");
           if (p1.length == 0)
              return [];
           else{
              var pl = p1[0];
              rest = p1[1];
              // extract the verb
              if (p1 == undefined || pl.length == 0){
                 this.errorList.push("!!!error on parsing propertylist!!!\n" +
                  "synchronizing is done on dot. Line: " +
                   s.substring(0, this.errLength));
                 return [];
              }
              var ts = this.makeTrSPL(sub, pl);
              // check for logical constants and do something
              // this is transferred to interface.js
              // ts = this.checkAnonInRule(ts);
              return [ts, rest];
           }
        }
      }
  }

// test the function parseAnonSet.
this.testParseAnonSet = function(){
   print("\ntestParseAnonSet\n****************\n");
   print( "[:b :c]." + this.parseObject("[:b :c].") + "\n");
//            print(( "", "[ :b :c; :e :f; :g :h, :i, :p]", 0), this.parseObject( "", "[ :b :c; :e :f; :g :h, :i, :p]", 0))
//            print(( "", "[ :b :c; :d [:e :f]; :g :h]", 0), this.parseObject ("", "[ :b :c; :d [:e :f]; :g :h]", 0))
}

this.parseAnonSet = function(as, s){
   /* parse a set of anonymous triples : insert an anonymous subject
    * and call parsePropertyList.
    */

   if (s == "")
      return [];
   else{
      var sd;
      var first;
      var subject;
      var pl;
      var pli;
      var rest;
      var ts;
      sd = skipBlancs(s);
      first = sd[0];
      // parse a set of anonymous triples: assign a subject
      // and then call parsePropertyList.
      if (first == "["){
          subject = this.createAnonSubject();
          //writeln("before parsePropertyList");
          pl = this.parsePropertyList([], sd.substring(1, sd.length));
          //writeln("after parsePropertyList::: " + pl);
          if (pl == undefined || pl.length == 0){
             this.errorList.push("!!!error parsing anonymous node. Line: " +
                  s.substring(0, this.errLength)  + "!!!END\n");
             return [];
          }else{
             pli = pl[0];
             rest = pl[1];
             ts = this.makeTrSPL(subject, pli);
             return this.parseAnonSet(concat(as,ts), rest);
          }
      // "]" found - insert "EndOfSet " and return.
      }else if (first == "]")
          return [as, sd.substring(1, sd.length)];
      // what happened?
      else{
          this.errorList.push("!!!error parsing anonymous node. Line: " +
                 s.substring(0, this.errLength));
          return [];
      }
    }
}

// make a list of triples from a subject and a propertylist
this.makeTrSPL = function(sub, pl){
   var ts = [];
   var p;
   var pr;
   var ol;
   var o;
   var t;
   for (var i = 0; i < pl.length; i++){
      p = pl[i];
      pr = p[0];
      ol = p[1];
      for (var i1 = 0; i1 < ol.length; i1++){
         o = ol[i1];
         t = new cTriple(sub, pr, o);
         ts.push(t);
      }
      //print("ts ==== " + ts + "\n");
      // ts = this.checkLogical(ts);
   }
   return ts;
}

// test the function parsePropertyList.
this.testParsePropertyList = function(){
    var pl;
    var rest;
    print("\ntestParsePropertyList\n*******************\n");
    p = this.parsePropertyList([], ":b :c; :d :e; :f :g.");
    if (p.length > 0){
       pl = p[0];
       rest = p[1];
       print(":b :c; :d :e; :f :g. rest: " + rest +
             " parsed: \n" + pl + "\n");
    }else
       print("failure parsing: :b :c; :d :e; :f :g.\n");
//            print(":b :c.", this.parsePropertyList([], ":b :c."))
//            print(":b :c; :d :e; :f :g:", this.parsePropertyList([], ":b :c; :d :e; :f :g:"))
//            print(":a, :b,:c", this.parsePropertyList([], ":a, :b,:c"))
//            p =  this.parsePropertyList([],":p [:a :b],[:c :d], [:e :f].")
//            if p <> []:
//                  [(pl, rest)] = p
//                  print (":p [:a :b],[:c :d], [:e :f]. rest: " + rest +\
//                         " parsed: \n" + tr.plToString(pl) + "\n")
//            else:
//                  print ("failure parsing: :p [:a :b],[:c :d], [:e :f].\n")
}

this.parsePropertyList = function(pl, s){
   // parses one or more properties.
   // returns a list of properties: [pl, reststring]
   //print("parsePropertyList string in = " + s + "\n");
   //writeln("entering parsePropertyList");
   if (s == "")
      return [];
   else{
      var p;
      var sd = skipBlancs(s);
      var first = sd[0];
      // end of propertyList
      if (sd.substring(0, 1) == "}")
          return [pl, s];
      // end of propertyList
      else if (sd.substring(0, 1) == ".")
          return [pl, s];
      // end of anonymous set
      else if (sd.substring(0, 1) == "]"){
          //writeln("] encountered.");
          return [pl, s];
      // propertylist with subject already defined.
      }else if (sd.substring(0, 1) == ";")
          p = this.parseProperty(sd.substring(1, sd.length));
      else{  // parse first (and maybe only) node
          p = this.parseProperty(sd);
          //writeln("property p parsed: " + p);

          if (pl.length > 0){
             // first property has been parsed already
             this.errorList.push("!!!missing ; while parsing propertylist!!! Line: " +
                               s.substring(0, this.errLength) + "\n");
             return [];
          }
      }
           if (p.length == 0)
             return [];
           else{
             var pr;
             var rest;
             pr = p[0];
             rest = p[1];
             if (pr == "n")
                 return [pl,rest];
             pl.push(pr);
             return this.parsePropertyList(pl, rest);
           }

    }
}

this.parseProperty = function(s){
   /* parse a single property.
    * a property is a pair (property, objectlist)
    * this function returns: [(property,reststring)] or []
    */
    this.inverseFlag = 0;
    if (s == "")
       return [];
    else{
       var sd = skipBlancs(s);
       var first = sd.substring(0, 1);
       if (first == "}")  // possibly ;}
          return ["n",sd];
       else if (first == "]")   // possibly ;]
          return ["n", sd];
       else if (first == ".")   // possibly ;.
          return ["n", sd];
       else{
          // "is" detected, set inverse flag
          if (sd.substring(0, 3) == "is"){
              sd = skipBlancs(s.substring(2, s.length));
              this.inverseFlag = 1;
          }
          var p = this.parseVerb(sd);
          //writeln("verb parsed: " + p);
          if (p.length == 0){
             this.errorList.push("!!!error parsing predicate!!! Line: " +
                   s.substring(0, this.errLength)   + "!!!!");
             return [];
          }
          var verb = p[0];
          var rest = p[1];
          if (this.inverseFlag)
             verb.isof = 1;
          p = this.parseNodeList([], rest);
          //writeln("nodelist parsed: " + p);
          if (p.length != 0){
             var nl = p[0];
             rest = p[1];
             return [[verb, nl], rest];
          }else
             return [];
       }
     }
}

// test the function parseNodeList.
this.testParseNodeList = function(){
   writeln("\ntestParseNodeList\n***********************\n");
   var p;
   var rl;
   var rest;
   p = this.parseNodeList([], ":a, :b,:c.");
   if (p.length != 0){
      rl = p[0];
      rest = p[1];
      print(":a, :b,:c. rest: " + rest + " parsed: \n" + rl + "\n");
   }else
      print("failure parsing: :a, :b, :c.\n");
   p = this.parseNodeList([], "[:a :b],[:c :d], [:e :f].");
   if (p.length != 0){
      rl = p[0];
      rest = p[1];
      print("[:a :b],[:c :d], [:e :f] rest: " + rest +
                         " parsed: \n" + rl  +"\n");
   }else
      print("failure parsing: [:a :b],[:c :d], [:e :f]\n");

//            p = this.parseNodeList([], ":a, :b :c.")
//            if p <> []:
//                  [(rl, rest)] = p
//                  print (":a, :b :c. rest: " + rest + " parsed: \n" + r.rlToString(rl)+ "\n")
//            else:
//                  print ("failure parsing: :a, :b :c.\n")
//            p = this.parseNodeList([], ":a, b,:c.")
//            if p <> []:
//                  [(rl, rest)] = p
//                  print (":a, b,:c. rest: " + rest + " parsed: \n" + r.rlToString(rl)+ "\n")
//            else:
//                  print ("failure parsing: :a, b,:c.\n")
//            p = this.parseNodeList([], ":a.")
//            if p <> []:
//                  [(rl, rest)] = p
//                  print (":a. rest: " + rest + " parsed: \n" + r.rlToString(rl)+"\n")
//            else:
//                  print ("failure parsing: :a.\n")
//            p = this.parseNodeList([], ":a, :b,:c")
//            if p <> []:
//                  [(rl, rest)] = p
//                  print (":a, :b,:c rest: " + rest + " parsed: \n" + r.rlToString(rl)+"\n")
//            else:
//                  print ("failure parsing: :a, :b, :c\n")
//            p = this.parseNodeList([], ":a, :b,:c")
}

this.parseNodeList = function(ol, s){
/* parses nodes separated by , .
 * nodelist = [Resource]
 * returns: [nodelist, reststring]
 * first call: parseNodeList ([], s)
 */

 var sd;
 var first;
 var p;
 var o;
 //print("parseNodeList s = " +s + "\n");
 if (s == "")
    return [];
 else{
    sd = skipBlancs(s);
    if (sd == "")
       return [];
    first = sd.substring(0, 1);
    if (first == "." || first == ";" || first == "]" || first == "}"){
       // higher separators -- return
       //writeln("nodelist parsed: " + ol + " rest " + sd);
       return [ol, sd];
    }
    else if (first == ","){   // parse the next node (= object)
         p = this.parseObject(sd.substring(1, sd.length));
         if (p.length == 0){
            this.errorList.push("!!!error while parsing nodelist!!! Line: "
                     + s.substring(s, this.errLength) + "!!!!");
            return [];
         }else{
            o = p[0];
            s = p[1];
            ol.push(o);
            return this.parseNodeList(ol, s);
         }
    }else{  // parse the first (and possibly last) node
         if (ol.length != 0){
            // first node has been parsed already
            this.errorList.push("!!! missing comma while parsing nodelist!!! Line: " +
                     s.substring(0,this.errLength));
            return [];
          }
          p = this.parseObject(sd);
          //print("Object parsed: " + p);
          if (p.length == 0){
              this.errorList.push("!!!error while parsing nodelist!!! Line: " +
                 s.substring(0, s.length) + "!!!!");
              return [];
          }else{
              o = p[0];
              s = p[1];
              ol.push(o);
              return this.parseNodeList(ol, s);
          }
     }
   }
}


// parse a subject .
this.parseSubject = function(s){
   return this.parseObject(s);
}

this.testParseVerb = function(){
   p = this.parseVerb(":v :o.");
   print("Test parseVerb: " + p[0] + " $$$ " + p[1] + "\n");
}

// parse a verb = property.
this.parseVerb = function(s){
   if (s.substring(0, 3) == "has"){   // has detected - must be skipped
      var sd1 = skipBlancs(s.substring(3, s.length));
      return this.parseObject(sd1);
   }else{
      return this.parseObject(s);
   }
}

//      def testParseObject(self):
//            p = this.parseObject(":c .")
//            print ("Test parseObject: ", pre.fst(p[0]).toString(),  pre.snd(p[0]))
//            p = this.parseObject("{{:a :b :c} :d {:e :f :g}} :h :j.")
//            print ("Test parseObject: ", pre.fst(p[0]).toString(),  pre.snd(p[0]))
//            p = this.parseObject("[ ont:first ?a; ont:rest ?b ]")
//            print ("Test parseObject: ", pre.fst(p[0]).toString(),  pre.snd(p[0]))

// parse an object.
this.parseObject = function(s){
 if (s == "")
   return [];
 else{
   var sd;
   var first;
   var bool;
   var parsed;
   var rest;
   var ret;
   var re;
   var p;
   var sd1;
   sd = skipBlancs(s);
   first = sd.substring(0,1);
   // print("parseObject sd " + sd + "\n");
   if (first == "{"){  // embedded sets
      p = this.parseTripleSet([], sd);
      if (p.length == 0){
         ret = this.synchronize1(s, "}");
         bool = ret[0];
         parsed = ret[1];
         rest = ret[2];
         if (bool == 0){
            this.errorList.push("Error parsing tripleset: missing }" + sd.substring(0, this.errLength));
            return [];
         }
       }else{
            re = new cResource("");
            re.set = p[0];
            re.simple = 0;
            return [re, p[1]];

       }
   }else if (first == "["){   // embedded anonymous sets

         p = this.parseAnonSet([], sd);
         //writeln("after parseAnonSet(): " + p);
         if (p == undefined || p.length == 0){
            ret = this.synchronize1(s, "]");
            bool = ret[0];
            parsed = ret[1];
            rest = ret[2];
            if (bool == 0){
               this.errorList.push("Error parsing tripleset: missing ] " + sd.substring(0,this.errLength));
               return [];
            }
         }else{
               re = new cResource("");
               re.set = p[0];
               re.simple = 0;
               return [re, p[1]];
         }
    }else if (sd.substring(0, 2) == "of"){   // of detected - must be skipped
            sd1 = skipBlancs(sd.substring(2, sd.length));
            return this.parseObject(sd1);
    }else{  // parse an object
            p = this.parseNode(skipBlancs(sd));
            if (p.length == 0){  //
               this.errorList.push("!!!error while parsing subject or object!!! Line: " +
                  s.substring(0, this.errLength) + "!!!!");
               return [];
            }
            re = p[0];
            rest = p[1];
            //print("parseObject parsed = " + re + " rest = " + rest + "\n");
            rest = skipBlancs(rest);
            if (rest.length > 2 && rest.substring(0, 1) == "."
                && elemS(rest.substring(1, 2), delimNode) == 0)
                return this.parsePath(1, re, rest);
            if (rest.length > 2 && rest.substring(0, 1) == "^"
                && elemS(rest.substring(1, 2), delimNode) == 0)
                return this.parsePath(2, re, rest);
            return p;
         }
  }
}



this.createAnonSubject = function(){
   /* create an anonymous subject; form= :T$$$n . */
   var s;
   var re;
   var nr;
   this.anonCounter = this.anonCounter + 1;
   s = ":T$$$" + this.anonCounter;
   re = new resource("");
   this.res(re, s,"",s);
   nr = resNrsInst.nextNumber();
   if (this.queryFlag)
     re.nr = -nr;
   else{
     re.nr = nr;
     this.resdic[s] = re;
   }
   re.cr = true;
   return re;
}

this.parseNode = function(s){
  /* function for parsing nodes.
     input is the string to be parsed.
     returns [resource, rest_string] or [] in case of error.
     Formats of a node (=URI):
       <#...>
       <>
       :...
       prefix:...
       <URI>
       "..."    (constant)
  */
  var y;
  var sd;
  var flabel;
  var ret;
  var bool;
  var re;
  if (s == "")
       return [];
  else{
    // parse all blanks
    s = skipBlancs(s);
    // get first character
    y = s.substring(0, 1);
    sd = s.substring(1, s.length);
    // starts with ":" This refers to the parsed document.
    if (y == ":")
         return this.parseNodeThis(sd);
    // starts with =>. This is log:implies
    else if (s.substring(0,2) == "=>"){
         flabel = log + "implies";
         ret = this.createRes(flabel);
         bool = ret[0];
         re = ret[1];
         if (bool == 0)
             this.res(re, flabel, "", "=>");
         return [re, skipBlancs(s.substring(3, s.length))];
    }
    // starts with "<" Three cases : <> <#..> <URI>
    else if (y == "<")
         return this.parseNodeLesser(sd);
    // starts with (
    else if (y == "(")
         return this.parseList(sd);
    // starts with "?:" This is a variable.
    else if (y == "?")
         return this.parseVariableQ(s);
    // starts with "_:" This is a variable.
    else if (y == "_")
         return this.parseVariable(s);
    // intercept special comment """
    else if (s.substring(0,3) == "\"\"\"")
         return this.parseSpecialComment(s.substring(3, s.length));
    // starts with '"' Constant
    else if (y == '"')
         return this.parseConstant(sd);
    // the verb is "a"
    else if (s.substring(0,1) == "a" &&
                 testBlancs(s.substring(1,2))){
         flabel = this.rdf + "type";
         ret = this.createRes(flabel);
         bool = ret[0];
         re = ret[1];
         if (bool == 0)
             this.res(re, flabel, "", "a");
         return [re, skipBlancs(sd)]
     }
     // skip "of" normally detected in parseObject
     else if (s.substring(0,2) == "of" &&
                     testBlancs(s.substring(2, 3)))
         return this.parseNode(s.substring(2, s.length));
     // "has" detected skip this normally detected in parseVerb
     else if (s.substring(0, 3) == "has" &&
                     testBlancs(s.substring(3, 4)))
         return this.parseNode(s.substring(3, s.length));
     // "this" detected
     else if (s.substring(0,4) == "this" &&
                    testBlancs(s.substring(4, 5))){
         flabel = this.getFromDictionary(":");
         ret = this.createRes(flabel);
         bool = ret[0];
         re = ret[1];
         if (bool == 0)
             this.res(re, flabel, "", ":");
         return [re, s.substring(5, s.length)];
     }
     // "is" detected, skip and set inverse flag (handled in parseTriple)
     else if (s.substring(0, 2) == "is" &&
                     testBlancs(s.substring(2, 3)))
         return this.parseNode(skipBlancs(s.substring(2, s.length)));
     // lonely : detected. Must be format: prefix:postfix.
     // The prefix must be known.
     else
         return this.parseNodePrefix(s);
  }
}

this.parsePath = function(bool, re1, s){
  /* parses a path. Returns a complex resource and a reststring
   * res is the first parsed node
   * Format: [res, rest]
   */
   var rest;
   var name;
   var bool1;
   var re;
   var triple;
   var p;
   var res1;
   var lastAnon;
   var cont;
   var dot;
   var hat;
   var triple1;
   var newAnon;
   var ret;
   rest = s.substring(1, s.length); // skip dot or ^
   // create a resource
   name = "list" + this.listCounter;
   this.listCounter += 1;
   ret = this.createRes(name);
   bool1 = ret[0];
   re = ret[1];
   if (bool1 == 0)
     this.res(re, name, ":", name);
   // get the next node
   p = this.parseNode(rest);
   if (p == []){
      this.errorList.push("Error parsing path" + rest.substring(0, this.errLength));
      return [];
   }
   res1 = p[0];
   rest = p[1];
   lastAnon = this.createAnonSubject();
   if (bool)  // a dot was detected; the resource is a subject
      triple = new cTriple(re1, res1, lastAnon);
   else  // a ^ was detected; the resource is an object
      triple = new cTriple(lastAnon, res1, re1);
   // add the triple
   re.set = [triple];
   re.simple = 0;
   // now parse the other nodes (if there are some) or stop
   cont = 1;
   while (cont){
      dot = 0;
      hat = 0;
      rest = skipBlancs(rest);
      // now detect whether next is a dot or a ^ or the end of the path
      if (rest.substring(0, 1) == "." &&
            elemS(rest.substring(0,1), delimNode) == 0)
         dot = 1;
      else if (rest.substring(0, 1) == "^" &&
            elemS(rest.substring(1, 2), delimNode) == 0)
         hat = 1;
      else  // apparently the path is finished
         return [re, rest];
      // parse the next node
      p = this.parseNode(rest.substring(1, rest.length));
      if (p == []){
        this.errorList.push("Error parsing path" + rest.substring(0, this.errLength));
        return [];
      }
      res1 = p[0];
      rest = p[1];
      // create a new triple
      newAnon = this.createAnonSubject();
      if (dot)
         triple1 = new cTriple(lastAnon, res1, newAnon);
      else
         triple1 = new cTriple(newAnon, res1, lastAnon);
      lastAnon = newAnon;
      re.set.push(triple1);
   }
}

this.toString = function(p){
    /* transform parsing result to string */
    return p[0].toString() + "/// " + p[1];
}

this.testParseNode = function(){
   /* test the function parseNode. */
//   print ("<> :a :b", "$$$Result: :",this.toString(this.parseNode ("<> :a :b")))
   //print (":]", "$$$Result: :",this.toString(this.parseNode (":]")))
   print (":a :b :c .\n$$$Result: :" + this.toString(this.parseNode (":a :b :c .\n")));
   print("dc:a dc:b dc:c . {<http://www.w3.org> dc:ho \"oke\".}\n");
   print("\n$$$Result: :" + this.toString(this.parseNode("dc:a dc:b dc:c . {<http://www.w3.org> dc:ho \"oke\".}"))+ "\n");
//            print ("<http://www.guido> dc:b dc:c .","$$$Result: :",
//                   this.toString(this.parseNode ("<http://www.guido> dc:b dc:c .")))
//            print (";<#pat> :a :b.","$$$Result: :", this.toString(this.parseNode (";<#pat> :a :b.")))
   print("<#pat> :a :b\n$$$Result: :" + this.toString(this.parseNode ("<#pat> :a :b\n")));
   print("\"Hallo\" dc:b dc:c . {<http://www.w3.org> dc:ho \"oke\".}\n" +
                   "$$$Result: :" + this.toString(this.parseNode ("\"Hallo\" dc:b dc:c . {<http://www.w3.org> dc:ho \"oke\".}\n")));
//            print ("<>", "$$$Result: :",this.toString(this.parseNode ("<> :a :b")))
//            print ("<pat> :a :b.", "$$$Result: :",this.toString(this.parseNode ("<pat> :a :b.")))
   print("\"\"\" hhh\nelklklke\"\"\"\n$$$Result: :" + this.toString(this.parseNode ("\"\"\" hhh\nelklklke\"\"\"\n")));
   print("_:ab :cc\n$$$Result:  " + this.toString(this.parseNode("_:ab :cc")) + "\n");

}

this.parseNodePrefix = function(s){
   /* parse a node with format prefix:postfix */
   var sd;
   var ret;
   var bool1;
   var prefix;
   var rest1;
   var bool2;
   var postfix;
   var rest2;
   var pre;
   var flabel;
   var bool;
   var re;
   sd = skipBlancs(s);
   if (sd == "")
       return [];
   else{
       ret = parseUntil(":", sd);
       bool1 = ret[0];
       prefix = ret[1];
       rest1 = ret[2];
       // format (Bool, String, String)
       ret = parseUntilDelim(delimNode,
                             skipBlancs(rest1));
       bool2 = ret[0];
       postfix = ret[1];
       rest2 = ret[2];
       // format (Bool, String, String)
       //print("prefix = " + prefix + "\n");
       pre = this.getFromDictionary(prefix + ":")
       //print("pre = " + pre + "\n");
       // normal case
       //writeln("prefix: " + pre + " postfix: " + postfix);
       if (bool1 && bool2 && pre != "Error"){
           flabel = pre + postfix;
           ret = this.createRes(flabel);
           bool = ret[0];
           re = ret[1];
           if (bool == 0)
               this.res(re, flabel, prefix, prefix + ":" + postfix);
           return [re, rest2];
        }else{ // error
           this.errorList.push("Error parsing prefix:postfix: " + s + "\n")
           return [];
        }
    }
}

this.parseConstant = function(inString){
   /* parse a constant */
   var ret;
   var bool;
   var re;
   if (inString == ""){
       ret = this.createRes("");
       bool = ret[0];
       re = ret[1];
       if (bool == 0){
          this.res(re,"","","");

       }
       re.constant = 1;
       return [(re, "")]

   }else{
       var bool1;
       var constant;
       var rest1;
       ret = parseUntil ("\"", skipBlancs (inString));
       bool1 = ret[0];
       constant = ret[1];
       rest1 = ret[2];
       // format (Bool, String, String)
       if (bool1){  //  found
           ret = this.createRes(constant);
           bool = ret[0];
           re = ret[1];
           if (bool == 0){
              this.res(re, constant,"",constant);
           }
           re.constant = 1;

           return [re, rest1];
       }else
           this.errorList.push("Error parsing constant: " + inString);
   }
   return [];
}

this.parseSpecialComment = function(inString){
   /* parse a special comment (starts with 3x") and skip it */
   var ret;
   var bool;
   var re;
   if (inString == ""){
       ret = this.createRes("");
       bool = ret[0];
       re = ret[1];
       if (bool == 0){
          this.res(re,"","","");
          re.constant = 1;
       }
       return [(re, "")]
    }else{
       var constant;
       var rest;
       ret = parseUntilString(inString, "\"\"\"");
       bool = ret[0];
       constant = ret[1];
       rest = ret[2];
       if (bool){
          ret = this.createRes(constant);
          bool = ret[0];
          re = ret[1];
          if (bool == 0){
             this.res(re, constant,"",constant);
             re.constant = 1;
          }
          return [re, rest.substring(3, rest.length)]
       }else{
          this.errorList.push("Error parsing special constant: " + inString);
          return [];
       }
     }
}

this.parseVariable = function(s){
   /* parse a node that starts with _: (global existential variable)
    */
   var ret;
   var bool1;
   var node1;
   var rest1;
   ret = parseUntilDelim(delimNode, s);
   bool1 = ret[0];
   node1 = ret[1];
   rest1 = ret[2];
   if (bool1){   // normal case
     var bool;
     var re;
     ret = this.createRes(node1);
     bool = ret[0];
     re = ret[1];
     if (bool == 0){
         // make the number negative
         re.nr = -re.nr;
         this.res(re, node1,"",node1);
         re.varType = "_";
     }
     return [re,rest1]
   }else  // error
     this.errorList.push("Error parsing variable (_:xxx) : " + s.substring(0, this.errLength));
   return [];
}

this.parseVariableQ = function(s){
   /* parse a node that starts with ? (local universal variable)
    * Is only entered in the dictionary at the triple level.
    * Scope is on triple level.
    */
    var ret;
    var bool1;
    var node1;
    var rest1;
    ret = parseUntilDelim(delimNode, s);
    bool1 = ret[0];
    node1 = ret[1];
    rest1 = ret[2];
    if (bool1){  // normal case
        var re;
        re = new resource("");
        this.res(re, node1,"", node1);
        re.varType = "?";
        return [re,rest1];
    }else{  // error
        this.errorList.push("Error parsing variable (?xxx) : " + pre.getfirst(s, this.errLength));
        return [];
    }
}

this.parseNodeThis = function(s){
   /* parse a node that starts with : */
   //writeln("parseNodeThis : " + s);
   if (s == "")
     return [];
   else{
     var bool1;
     var node1;
     var rest1;
     var bool;
     var re;
     var ret = parseUntilDelim(delimNode, s);
     bool1 = ret[0];
     node1 = ret[1];
     rest1 = ret[2];
     //writeln("node1 = " + node1 + " s: " + s);
     if (bool1){
        if (node1.substring(0, 4) == "G$$$" ||
            node1.substring(0, 4) == "E$$$" ||
            node1.substring(0, 4) == "T$$$")
             flabel = ":" + node1;
        else
             flabel = this.getFromDictionary(":") + node1;

        ret = this.createRes(flabel);
        bool = ret[0];
        re = ret[1];
        if (bool == 0)
           this.res(re, this.getFromDictionary(":")+ node1,":",  ":" + node1);
        //writeln("parseNodeThis: " + re + " rest: " + rest1);
        return [re,rest1];
     }else{  // an error has happened
        this.errorList.push("Error parsing  : node " + s + "\n");
        return [];
     }
   }
}
         
this.parseNodeLesser = function(s){
  /* parse a node that starts with < */
  if (s == "")
     return [];
  else{
     var bool1;
     var rest1;  
     var flabel; 
     var bool;
     var re;
     var bool2;
     var rest2;
     var bool3;
     var node1;
     var rest3;
     var bool4;
     var node2;
     var rest4;    
     var ret = takec(">", skipBlancs(s));
     bool1 = ret[0];
     rest1 = ret[1];   
     if (bool1){       // parse <> = the parsed document
        flabel = this.getFromDictionary(":");
        ret = this.createRes(flabel);
        bool = ret[0];
        re = ret[1];
        if (bool == 0)
           this.res(re, flabel, ":", "<>");
        return [re,rest1];
     }else{
        ret = takec("#", skipBlancs1(s));
        bool2 = ret[0];
        rest2 = ret[1]; 
        ret = parseUntil(">", skipBlancs (rest2));
        bool3 = ret[0];
        node1 = ret[1];
        rest3 = ret[2];
        // parse <#...>                   
        if (bool2 && bool3){
           ret = this.getFromDictionary(":");
           flabel = ret.substring(0, ret.length-1) + "#" + node1;
           ret = this.createRes(flabel);
           bool = ret[0];
           re = ret[1];
           if (bool == 0)
              this.res(re, flabel, ":", "<#" + node1 + ">");
           return [re, rest3];
         }else{
           ret = parseUntil(">", skipBlancs(s));
           bool4 = ret[0];
           node2 = ret[1];
           rest4 = ret[2];
           if (bool4){   // parse <URI>
              ret = this.createRes(node2);
              bool = ret[0];
              re = ret[1]; 
              if (bool == 0)
                 this.res(re,node2,"", "<" + node2 +">");
              return [re, rest4];
            }else
              this.errorList.push("Error missing > :" + s + "\n");
              return [];
          }
        }
     }
}


this.createRes = function(label){
    /* create a resource
       update the current resource number after creating
       check if the resource exists already
       input is the full label of the resource
       output is a boolean and a resource"""
     */
     var ret = this.resdic[label];  
     if (ret != undefined)
         return [1, this.resdic[label]];
     else{
         re = new resource("");
         this.resdic[label] = re;
         return [0, re];
       }
}

this.res = function(resource, fullnameIn, abbrevIn, labelIn){
   resource.simple = 1;
   resource.uri = fullnameIn;
  // resource.abbrev = abbrevIn;
  // resource.label = labelIn;
}

this.parseList = function(s){
    /* function for parsing a list
     * Format: (x1 x2 ... xn)
     * Returns: [(list, reststring)]
     */
     var ret;
     var bool;
     var parsed;
     var rest;
     //print("parseList s = " + s + "\n");
     ret = this.synchronize1(s, ")");
     bool = ret[0];
     parsed = ret[1];
     //print("parsList ret = " + ret + "\n");
     rest = ret[2];
     if (bool == 0){
        this.errorList.push("!!! error parsing list missing )!!!");
        return [];
     }
     if (s == "")
        return [];
     else{
        var list;
        var sd;
        var cont;
        var p;
        var re1;
        var node;  
        var re;
        list = [];   
        sd = skipBlancs(s);
        cont = 1;
        while (cont){
           p = this.parseObject(sd);
           if (p == []) // error
              return [];
           re1 = p[0];
           rest = p[1];
           list.push(re1)
           sd = skipBlancs(rest);
           if (sd.substring(0, 1) == ")")
              cont = 0;
         }      
         node = "RDFE:list" + this.listCounter;
         ret = this.createRes(node);
         bool = ret[0];
         re = ret[1];
         if (bool == 0)
             this.res(re, node,"", node);
         re.RDFList = list;
         re.list = true;
         this.listCounter += 1;
         // print("parseList list = " + list + " sd = " + sd + "\n");
         return [re, sd.substring(1, sd.length)];   
       }
}

//      def parseParam(self, s):
//            """ function for parsing parameters that determine the
//                parsing process.
//                input is the string to be parsed.
//                returns a triple and the rest string
//                format of a param :
//                @param name value
//                A triple is made: RDFE:name RDFE:param value_of_param
//                The value is normally: "0" or "1"
//            """    
//
//            if s == "":
//               return []
//            else:
//               sd = utils.skipBlancs(s)
//               bool1, rest1 = utils.parseString( "@param", sd) 
//               bool2, name, rest2 = utils.parseUntil (" ", utils.skipBlancs1 (rest1))
//               bool3, value, rest3 = utils.parseUntil (".", utils.skipBlancs1(rest2))
//               if (bool1 == "T" and bool2 == "T" and bool3 == "T"):
//                      if name == "full_generation":
//                            if utils.startsWith(value,"0") == "T":
//                                  this.full_generation = 0
//                            elif utils.startsWith(value,"1") == "T":
//                                  this.full_generation = 1       
//                            else: # error
//                                  return []
//                      triple = tr.Triple()
//                      (bool, re) = this.createRes("RDFE:" + name)
//                      if bool == "F": # resource does not exist
//                            re.res("RDFE:" + name,"RDFE:","RDFE:" + name)
//                      triple.subject = re
//                      (bool, re) = this.createRes("RDFE:param")
//                      if bool == "F":
//                            re.res("RDFE:param", "RDFE:" , "RDFE:param")
//                      triple.predicate = re
//                      (bool, re) = this.createRes(value)
//                      if bool == "F":
//                            re.res(value,"",value)
//                            re.const = "T"
//                      triple.object = re
//                      return [(triple, utils.skipBlancs(rest3))]
//               else:  # an error has happened
//                      return []

               
this.getFromDictionary = function(s){
   /* get an entry from the dictionary */
      var ret = this.prefixDictionary[s];
      if (ret != undefined)
         return ret;
      else
         return "Error";
}
 
//    
//#
//# The bnf grammar
//#----------------------
//#
//#  Taken from <http://www.w3.org/DesignIssues/Notation3.html>
//#  on 2001-08-03 (version of 2001-04-10)
//#
//#  Modifications:
//#     
//# $Log: N3EParser.js,v $
//# Revision 1.4  2009/10/03 22:35:21  naudts
//# implementation of declarative negation + bug fixes
//#
//# Revision 1.3  2009/08/16 20:01:06  naudts
//# adding javascript builtins + corrections
//#
//# Revision 1.2  2005/02/24 17:21:38  naudts
//# procedures
//#
//# Revision 1.1  2005/01/28 23:44:37  naudts
//# 29/1/05
//#
//# Revision 1.4  2001/08/06 20:56:21  sandro
//# added space* and space+ in several places
//# removed "#" from forbidden chars in URI_Reference
//# handles comments
//# made directives actually part of the grammar (!)
//# allowed nprefix to be zero-length
//#
//# Revision 1.3  2001/08/03 13:44:43  sandro
//# filled in remaining non-terminals
//#
//# Revision 1.2  2001/08/03 13:02:48  sandro
//# standardized BNF so blindfold can compile it
//#    added ::= for each rule
//#    added | for branches
//#    added ; at end of rule
//#    added # before comments
//#    put quotes around literals
//#    turn hypen into underscore in identifiers
//#    rename prefix to nprefix (hack around blindfold keyword for now)
//#
//# Revision 1.1  2001/08/03 12:34:38  sandro
//# added opening comments
//#
//#
//#
//# document ::= void 
//#           | statementlist;
//#
//# space ::= " " | "\n" | "\r" | comment;
//#
//# comment ::= "#" [^\r\n]*;
//#
//# statement ::= subject space+ property_list
//#            | directive
//#            ;
//#
//# statementlist ::= (statement space* ("." space*)?)* ;
//#
//# subject ::= node;
//#
//# verb ::= ">-" prop "->"    # has xxx of 
//#       | "<-" prop "<-"    # is xxx of 
//#    #  | operator          # has operator:xxx of??? NOT IMPLMENTED
//#       | prop              # has xxx of -- shorthand
//#       | "has" prop        # has xxx of
//#       | "is" prop "of"    # is xxx of
//#       | "a"               # has rdf:type of
//#       | "="               # has daml:equivalent of
//#       ;
//#
//# prop ::= node;
//#
//# node ::= uri_ref2 
//#       | anonnode
//#       | "this"
//#       | node 
//#       ;
//#
//# nodelist ::= void    # (used in lists) 
//#           | node
//#           | node nodelist
//#           ;
//#
//# anonnode ::= "[" property_list "]"  # something which ...
//#           | "{" statementlist "}"  # the statementlist itself as a resource
//#           | "(" nodelist ")"       # short for eg [ n3:first node1; n3:rest [ n3:first node2; n3:rest: n3:null ]]
//#           ;
//#
//# property_list ::= void   # to allow [...]. 
//#                | verb space+ object_list
//#                | verb space+ object_list space+ ";" space+ property_list
//#                | ":-" anonnode  #to allow two anonymous forms to be given eg [ a :Truth; :- { :sky :color :blue } ] )
//#                | ":-" anonnode ";" property_list
//#                ;
//#
//# object_list ::= object 
//#              | object "," object_list
//#              ;
//#
//# uri_ref2 ::= qname 
//#           | "<" URI_Reference ">"
//#           ;
//#
//# qname ::= nprefix ":" localname; # ??? Allow omit colon when prefix void - keyword clash 
//#
//# object ::= subject 
//#         | string1 # " constant-value-with-escaping "
//#         | string2 # """ constant value with escaping including single or double occurences of quotes and/or newlines 
//#         #      well-formed-xml-element ???? legacy or structured stuff - not implemented or distinguished
//#         ;
//#
//# directive ::= "bind" space+ nprefix ":" uri_ref2   # Namespace declartion. Trailing "#" is omitted & assumed. Obsolete.
//#            | "@prefix" space+ nprefix ":" space+ uri_ref2  # Namespace declaration
//#            ;
//#
//// operator ::=  (Not implemented) 
////      + >- operator:plus -> 
////      - >- operator:minus ->
////      / >- operator:slash->
////      * >- operator:star-> (etc? @@)
//#
//# fragid ::= alpha alphanumeric* ;
//#
//# alpha ::= [a-zA-Z];
//#
//# alphanumeric ::= alpha | [0-9] | "_";
//#
//# void ::= "" ;   # nothing
//#
//# URI_Reference ::= [^{}<>]*;    # short version
//#
//# nprefix ::= "" | ((alpha | "_") alphanumeric*);
//#
//# localname ::= fragid;
//#
//# string1 ::= '"' string1_char* '"';
//#
//# string1_char ::= '\\"' | [^\"] ;           # should disallow some other characters, etc.
//#
//# string2 ::= '"""' string2_char* '"""';
//#
//# string2_char ::= [^"] | ([^] [^] [^"]);    # something like this; need to think about it some more
//#
//#-----------------------------------------------------------------------}
//
}
