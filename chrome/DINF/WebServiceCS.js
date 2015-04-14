function WebServiceCS(){

    this.applicationDict = new HashTable();

    var soapResp1 = "<?xml version='1.0'?>" +
                      "<soap:Envelope " +
                        "xmlns:soap='http://www.w3.org/2001/12/soap-envelope' " +
                        "soap:encodingStyle='http://www.w3.org/2001/12/soap-encoding'>" +
                        "<soap:Body xmlns:em='http://eulermoz/soap#'>" +
                          "<em:Response> <em:Application>";
    var soapResp2 = "</em:Application>";
    var soapResp3 = "</em:Response>" +
                        "</soap:Body>" +
                       "</soap:Envelope>";

    this.forwardCS;
    this.inferenceType = "forward";


    /**
      * Example input:
      * Thread 1 recieved: POST / HTTP/1.1
      * Host: 127.0.0.1
      * User-Agent: Mozilla/5.0 (Windows; U; Windows NT 5.1; es-ES; rv:1.9.1.3) Gecko/20090824 Firefox/3.5.3
      * Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*\/*;q=0.8
      * Accept-Language: es-es,es;q=0.8,en-us;q=0.5,en;q=0.3
      * Accept-Encoding: gzip,deflate
      * Accept-Charset: ISO-8859-1,utf-8;q=0.7,*;q=0.7
      * Keep-Alive: 300
      * Connection: keep-alive
      * Content-Type: text/plain;charset=UTF-8
      * Content-Length: 322
      * Origin: null
      * Pragma: no-cache
      * Cache-Control: no-cache
      *
      * <soap:Envelope xmlns:soap='http://www.w3.org/2001/12/soap-envelope' soap:encodingStyle='http://www.w3.org/2001/12/soap-encoding'><soap:Body xmlns:em='http://eulermoz/soap#'><em:Query> <em:Application>authen</em:Application>@prefix : &lt;authen#&gt;.
      * ?who :authenticated ?mailinglist.</em:Query></soap:Body></soap:Envelope>
      * Author: Guido J.M. Naudts Bouwel
      */
    this.extractXML = function(requestIn){
        var i = requestIn.indexOf("<soap:Envelope");
        return requestIn.substring(i);
    };

    /**
      * http header example:
      * HTTP/1.1 200 OK
      * Content-Type: text/xml; charset=utf-8
      * Content-Length: length
      */
      this.makeResp = function(application, sols){
          // make soap  message
          var so = "";
          //writeMessage("array " + arrayToString(sols));
          for (var i = 0; i < sols.length; i++){
              so = so + "<em:Solution>";
              for (var k = 0; k < sols[i].length; k++){
                  so = so + encodeHTML((sols[i][k]).toString());
              }
              so = so + "</em:Solution>";
          }
          var s = soapResp1 + application + soapResp2 + so + soapResp3;
          var s1  = "HTTP/1.1 200 OK\nContent-Type: text/plain;charset=UTF-8\nContent-Length: ";
          s1 = s1 + s.length + "\n\n" + s ;
          return s1;
      };



    /**
     * When the serviceObject is non null,
     * the fileName will be asked from the serviceobject.
     *
     */
    this.acceptSoapInit = function(soapMessage, serviceObject){
        //writeln("soap message: " + soapMessage);
        var myXML = new XML(soapMessage);
        var em = new Namespace('http://eulermoz/soap#');
        //writeln("soapMessage " + arrayToString(soapMessage));
        this.application = myXML..em::Application;
        //writeln("application = " + this.application);
        var query = myXML..em::Query.text()[0].toString();
        //writeln("Query: " + query);
        var appFileName;
        if (serviceObject != undefined){
            appFileName = serviceObject.WSMap[this.application];
        }else{
        // must get the filename of the application
            appFileName = getBasePath() + "wsApps\\" + this.application + ".n3";
        }
        // must execute some reasoning now
        interface = new XULInterface();
        //writeln("file == " + appFileName);
        interface.addSetByFilename(this.application, "a", appFileName);
        interface.addSetByString("q1", "q", query);
        //writeln("interface.N3setBuffer " + interface.N3setBuffer[this.application]);
        interface.makeInfDB("pdb", [this.application] );
        //writeln("Application: " + interface.getSet("pdb", this.application) + "Query: " + interface.getSource("q1"));
        this.forwardCS = this.initQuery(interface, "pdb", "q1");
        // for testing
        //this.forwardCS.inf.verbose = true;
//        var sols1 = interface.queryInfDB("pdb", "q1", "forward" );
//        writeln("sols1 = " + sols1);
//        return [application, sols1];
    };

    this.serverNextStep = function(){
         return this.forwardCS.performStep();
    };

    this.initQuery = function(interface, dbName, queryName){
        /* dbName: name of a db
         * queryName: name of a queryfile
         * inferenceType: actually two choices: "forward" and "backward"
         * Return: an array of arrays.
         *   The second order arrays are arrays of strings
         *   in N3 format; each string array represents a solution
         *   i.e. the query with all variables substituted
         *   by resources.
         *     Example: queryInfDB("myDB", "query", "backward");
         */
         // the state of the infData variables must be saved in vector inf.stateSave
         // so the state can be restored for a new query


         var inferenceType = this.inferenceType;
         var inf = interface.infList[dbName];
         if (inf.stateSave == undefined)
            inf.stateSave = [inf.resdic, inf.currRes, inf.anonCounter, inf.locCounter,
                inf.existCounter, inf.listCounter, inf.ruleNr, inf.tripleNr];
         else{
            inf.resdic = inf.stateSave[0];
            inf.currRes = inf.stateSave[1];
            inf.anonCounter = inf.stateSave[2];
            inf.locCounter = inf.stateSave[3];
            inf.existCounter = inf.stateSave[4];
            inf.listCounter = inf.stateSave[5];
            inf.tripleNr = inf.stateSave[6];
         }
         var n3Parser  = new N3EParser();
         n3Parser.queryFlag = 1;
         var set = interface.N3setBuffer[queryName];
         //print("setBuffer query "+ arrayToString(this.N3setBuffer[queryName][2]) + "\n");
         var ret = getRDFDB1(set[2], inf, n3Parser);
         //writeln("XULInterface.queryInfDB ret = " + ret);
         // do some infData manipulations
         inf = ret[1];
         dbi = new db(ret[0]);

         dbi.makePropertyDict();
         //print("dbi " + dbi.ts + "\n");
         inf.dslist.push(dbi);
         if (inf.dslist.length > 0){
           inf.graphs = subArray(inf.dslist, 0, inf.dslist.length-1);
           inf.goallist = inf.dslist[inf.dslist.length-1].ts;
         }
         inf.query = [];
         inf.goallistSav = [];
         inf.querySav = [];
         //print("XULInterface inf.goallist = " + inf.goallist)

         for (var i = 0; i <  inf.goallist.length; i++) {
             inf.query.push(copyTriple(inf.goallist[i]));
             inf.goallistSav.push(copyTriple(inf.goallist[i]));
             inf.querySav.push(copyTriple(inf.goallist[i]));
         }
         //print("XULInterface inf.query = " + inf.query)
         inf.tripleNr = inf.initinf1(inf.tripleNr);
         inf.nooutput = 1;
         //inf.verbose=true;
         //inf.maxSteps = 50;
         if (inferenceType == "backward"){
            // not yet supported
            // inference(inf);
         }
         if (inferenceType == "forward"){
            // initialize the reentrant version
            reasonCS = new ReasonCS(inf);
            inf.dslist.pop();
            return reasonCS;

         }
         return null;
    };
}