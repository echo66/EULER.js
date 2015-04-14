function WebService(){

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
          var s = soapResp1 + encodeHTML(application) + soapResp2 + encodeHTML(sols) + soapResp3;
          var s1  = "HTTP/1.1 200 OK\nContent-Type: text/plain;charset=UTF-8\nContent-Length: ";
          s1 = s1 + s.length + "\n\n" + s ;
          return s1;
      }


    this.acceptSoap = function(soapMessage, serviceObject){
        var myXML = new XML(soapMessage);
        var em = new Namespace('http://eulermoz/soap#');
        //writeln("soapMessage " + arrayToString(soapMessage));
        var application = myXML..em::Application;
        //writeln("application = " + application);
        //writeln("Application: " + application);
        var query = decodeHTML(myXML..em::Query.text()[0].toString());
        //writeln("Query: " + query);
        // must get the filename of the application
        var appFileName = getBasePath() + "wsApps\\" + application + ".n3";
        // must execute some reasoning now
        interface = new XULInterface();
        //writeln("file == " + appFileName);
        interface.addSetByFilename(application, "a", appFileName);
        interface.addSetByString("q1", "q", query);
        //writeln("interface.N3setBuffer " + interface.N3setBuffer[application]);
        interface.makeInfDB("pdb", [application] );
        //writeln("Application: " + interface.getSet("pdb", application) + "Query: " + interface.getSource("q1"));
        var sols1 = interface.queryInfDB("pdb", "q1", "forward" );
        //writeln("sols1 = " + sols1);
        return [application, sols1];


    }
}

function getSolsFromSoap(soapIn){

    // eliminate the xml version declaration because it gives an error!!
    // also eliminate the http header
    soapIn = elimVersion(soapIn);
    //writeMessage("soapIn = " + soapIn);

    var myXML = new XML(soapIn);

    var em = new Namespace('http://eulermoz/soap#');

    var sols = myXML..em::Solution;
    var elm;
    var s = "";
    var i = 0;
    for each (elm in sols){
        s = s + "Solution " + i + ":\n" + elm + "\n";
        i++;
    }
    /*var s = "";
    writeMessage("WebServiceH.getSolsFromSoap: " + sols);
    for (var i = 0; i < sols.length; i++){
        s = s + "Solution " + i + ":\n";
        s = s + sols[i];
    }
    writeMessage("sss = " + s);*/
    return  s ;
}

function elimVersion(xmlIn){
    var i = xmlIn.indexOf("<?xml");
    var k = xmlIn.indexOf("?>", i);
    return xmlIn.substring(k+2);
}
