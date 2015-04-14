/**
 * This object contains the web services api; it contains the necessary functions and
 * data structures for web services.
 * Author: Guido J.M. Naudts Bouwel
 */
function WebService(){

    this.port;

    this.wsServerCS;

    // the map with name and fileName of the web services
    this.WSMap;

    // the map with the name of the queries and the queries
    this.queryMap;

    /**
      * start the web service
      * In our system there is only one webservice object running for all possible web services.
      * Optionally teh default port number can be changed
      */
    this.startWebService = function(port){
        if (port == undefined){
            this.port = 10000;
        }else{
            this.port = port;
        }
        this.wsServerCS = new WSserverCS();
        this.wsServerCS.port = WSPort;
        this.wsServerCS.start();
        // when the WS server has a non null serviceobject he will 
        this.wsServerCS.serviceObject = this;

    }

    /**
      * Stop the web service
      */
    this.stopWebService = function(){
        wsServerCS.stop();
    }

    /**
      * Add a query to a list of queries.
      * a query has a name.
      */
    this.addQuery = function(name, query){
        this.queryMap[name] = query;
    }

    /**
      * Retrieve a query from a list of queries.
      */
    this.getQuery = function(name, query){
        return this.queryMap[name];
    }

    /**
      * retrieve the list of queries
      */
    this.getQueryList = function(){
         return this.queryMap;
    }

    /**
      * add a webservice axiom file
      */
    this.createWebService = function(name, fileName){
        this.WSMap[name] = fileName;
    }

    /*
     * Get the list of webservice axiom files
     */
    this.getWSList = function(){
        return this.WSMap;
    }

    /**
      * query a webservice. The parameter webservice is the name of the webservice.
      * The solution is returned as a N3 set.
      */
    this.queryWS = function(webServiceAddress, webServiceName, query){
            // we got all info, we can make the query
            var i =  webServiceAddress.indexOf(":");
            var port = 10000;
            var address;
            if ( i > 0 ){
               port = wsAddress.substring(i+1);
               address = wsAddress.substring(0,i);
            }else{
               address = wsAddress;
            }
            var wsClient = new WSclientO;
            return wsClient.query(webServiceName, query, address, port);
    }

    this.test = function(){
        startWebService();
        this.createWebService
    }

}