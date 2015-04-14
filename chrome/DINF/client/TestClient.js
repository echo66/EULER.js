function TestClient(){
    /**
      * This a client that starts a query but does not wait for the answer.
      * This is for testing the concurrency.
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

    this.exampleRequest1 =  "<em:Query> <em:Application>gedcom.axiom</em:Application>" +
                              "@prefix gc: &lt;http://www.daml.org/2001/01/gedcom/gedcom#&gt;." +
                              "?who1 gc:father ?who2." +
                            "</em:Query>";

    this.postHeader = "POST / HTTP/1.0\n" +
                      "User-Agent: DINF\n" +
                      "Content-Type: application/x-www-form-urlencoded\n" +
                      "Content-Length: ";



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
        message = this.postHeader + message.length + "\n\n" + message;
        netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
        var transportService =
          Components.classes["@mozilla.org/network/socket-transport-service;1"]
            .getService(Components.interfaces.nsISocketTransportService);
        this.transport = transportService.createTransport(null,0,destination,port,null);

        this.outstream = this.transport.openOutputStream(0,0,0);
        //writeln("Write to socket now." );
        this.outstream.write(message, message.length);


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
        return "GET " + address + " HTTP/1.1\n";

    };

    this.test = function(){
        this.send("www.yahoo.com/", 80, this.makeHeader("www.yahoo.com:80"));

    };

    this.test1 = function(destination, port){

        this.send(destination, port, this.soapPart1 + this.exampleRequest1 + this.soapPart2);
    };
}