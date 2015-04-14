function WSclientO(){
    /**
      * Author: Guido J.M. Naudts Bouwel
      */


    this.soapPart1 =  "<soap:Envelope " +
                          "xmlns:soap='http://www.w3.org/2001/12/soap-envelope' " +
                          "soap:encodingStyle='http://www.w3.org/2001/12/soap-encoding'>" +
                          "<soap:Body xmlns:em='http://eulermoz/soap#'>";

    this.soapPart2 =  "</soap:Body>" +
                         "</soap:Envelope>";

    this.exampleRequest =  "<em:Query> <em:Application>authen</em:Application>" +
                              "@prefix : &lt;authen#&gt;.\n" +
                              "?who :authenticated ?mailinglist." +
                           "</em:Query>";

    this.requestPart1 = "<em:Query> <em:Application>";

    this.requestPart2 = "</em:Application>";

    this.requestPart3 =  "</em:Query>";

    this.postHeader = "POST /fromDINF.sjs HTTP/1.0\n" +
                      "User-Agent: DINF\n" +
                      "Content-Type: application/x-www-form-urlencoded\n" +
                      "Content-Length: ";

    this.recieved;

    /**var soapExample1 =  "<soap:Envelope " +
     "xmlns:soap='http://www.w3.org/2001/12/soap-envelope' " +
     "soap:encodingStyle='http://www.w3.org/2001/12/soap-encoding'>" +
     "<soap:Body xmlns:em='http://eulermoz/soap#'>" +
     "<em:Query> <em:Application>authen</em:Application>" +
     "@prefix : <authen#>;.\n" +
     "?who :authenticated ?mailinglist." +
     "</em:Query>" +
     "</soap:Body>" +
     "</soap:Envelope>"; */
    /**
     * <em:Query> <em:Application>authen</em:Application>
     * <em:ObjectString/>
     * MailingList
     *
     * </em:Query>
     *
     * <em:ObjectString> means that the recieving server will replace MailingList
     * with: [em:ObjectString "MailingList"].
     * This can then match with a rule eg
     * { some antecedents } => {[em:ObjectString "MailingList"]}.
     * (The same mechanism will be used in the output of the server ie
     * if the result of the query is: [em:ObjectString "some_string"].
     * only the string will be returned in the response.
     */
    /*
     * Author: Guido J.M. Naudts 11/3/52
     */


    this.instream;
    this.outstream;
    this.transport;
    this.ro;

    this.send = function(destination, port, message){
      try{
        //message = this.postHeader + message.length + "\n\n" + message;
        netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
        var transportService =
          Components.classes["@mozilla.org/network/socket-transport-service;1"]
            .getService(Components.interfaces.nsISocketTransportService);
        this.transport = transportService.createTransport(null,0,destination,port,null);
        this.ro = new readObject(this.transport);
        this.ro.init();

        this.outstream = this.transport.openOutputStream(0,0,0);
        //writeln("WSclientO.send Write to socket now.Message: " + message );
        this.outstream.write(message, message.length);

        var rec = "";
        while(rec == ""){
            rec = this.ro.read();
            nsWaitForDelay(10);
        };
        //writeln("Recieved: \n" + rec + "\n");
        this.recieved = rec;
        this.stop();

      }catch(ex){
         writeln("send: " + ex.description);
      }
    };




    this.stop = function()
    {
      netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
           this.ro.close();
           this.outstream.close();
           this.transport.close("EOT");


    };


    this.makeHeader = function(address){
        return "GET " + address + " HTTP/1.1\n\n";

    };

    this.test = function(){
        this.send("www.yahoo.com/", 80, this.makeHeader("www.yahoo.com:80"));

    };

    this.test1 = function(destination, port){

        this.send(destination, port, this.soapPart1 + this.exampleRequest + this.soapPart2);
    };

    this.query = function(service, query, destination, port){
        this.send(destination, port, this.soapPart1 + this.requestPart1 + encodeHTML(service) +
                 this.requestPart2  +   encodeHTML(query) + this.requestPart3 + this.soapPart2
                );
    }

    this.postExample = "POST /fromDINF.sjs HTTP/1.0\n" +
        "From: DINF\n" +
        "User-Agent: DINF\n" +
        //"Host: localhost:6673/fromDINF.sjs\n" +
        "Content-Type: x-www-form-urlencoded\n" +
        "Content-Length: " + encodeHTML("userid=joe&password=guessme").length +"\r\n\r\n" +
        encodeHTML("userid=joe&password=guessme");

    this.testPow = function(){
        writeln("WSclientO.testPow");

        //this.send("localhost",6673, this.makeHeader("http://localhost:6673/fromDINF.sjs"));
        var mess =  encodeHTML(this.soapPart1 + this.requestPart1 + "authen" +
                 this.requestPart2  +   query + this.requestPart3 + this.soapPart2);
        this.send("localhost", 6673,  this.postHeader + mess.length + "\r\n\r\n" + mess);
        //this.send("localhost", 6673, this.makeHeader("/test.html")); // ok
        //post_to_url("http://localhost:6673/fromDINF.sjs",{"a":"q"}); //nok
    }

    function writeln(text){
           if (application.document.getElementById('resultsText') == undefined){
               document.writeln(text);
           }else{
               application.document.getElementById('resultsText').value =
                   application.document.getElementById('resultsText').value + text + "\n";
           }
    }

}