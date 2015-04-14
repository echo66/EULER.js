/**
  * Author: Guido J.M. Naudts Bouwel
  */

var order = new XML()

order=
<order id="555">
<date>2005-08-01</date>
<customer>
   <firstname>John</firstname>
   <lastname>Johnson</lastname>
</customer>
<item>
   <name>Maxilaku</name>
   <qty>5</qty>
   <price>155.00</price>
</item>
</order>;

var XMLexample = "<?xml version='1.0' encoding='ISO-8859-1'?>" +
              "<!-- Edited by XMLSpy® -->" +
              "<!DOCTYPE note [\n" +
        /*         "<!ELEMENT note (to,from,heading,body)>\n" +*/
                 "<!ELEMENT to (#PCDATA)>\n" +
                 "<!NOTATION GIF SYSTEM 'image/gif'>\n" +

            /*     "<!ELEMENT from (#PCDATA)>\n" +
                 "<!ELEMENT heading (#PCDATA)>\n" +
                 "<!ELEMENT body (#PCDATA)>\n"*/

                 "<!ENTITY test 'test'>" +
              "\n]>" +

              "<?myTest vari='none'?> " +
              "<note>" +
                 "<![CDATA[<test><ok/><test> ]]>" +
                  "<t>&test;</t>"+
	              "<to type='message' importance='low'>Tove</to>" +
	              "<from>Jani</from>" +
	              "<heading>Reminder</heading>" +
	              "<body>Don't forget me this weekend!</body>" +
              "</note>\n";

var soapExample1 = //"<?xml version='1.0'?>" +
                  "<soap:Envelope " +
                    "xmlns:soap='http://www.w3.org/2001/12/soap-envelope' " +
                    "soap:encodingStyle='http://www.w3.org/2001/12/soap-encoding'>" +
                    "<soap:Body xmlns:em='http://eulermoz/soap#'>" +
                      "<em:Query> <em:Application>authen</em:Application>" +
                      "@prefix : &lt;authen#&gt;.\n" +
                      "?who :authenticated ?mailinglist." +
                      "</em:Query>" +
                    "</soap:Body>" +
                   "</soap:Envelope>";

var soapExample2 = "<?xml version='1.0'?>" +
                  "<soap:Envelope " +
                    "xmlns:soap='http://www.w3.org/2001/12/soap-envelope' " +
                    "soap:encodingStyle='http://www.w3.org/2001/12/soap-encoding'>" +
                    "<soap:Body xmlns:em='http://eulermoz/soap#'>" +
                      "<em:Response> <em:Application>authen</em:Application>" +
                      "':a log:notEqualTo :b.\n" +
                      ":c log:notEqualTo :d.'" +
                      "</em:Response>" +
                    "</soap:Body>" +
                   "</soap:Envelope>";

var wsdlExample =
        "<?xml version='1.0'?>" +
"<definitions xmlns='http://schemas.xmlsoap.org/wsdl/'" +
        " xmlns:soap='http://schemas.xmlsoap.org/soap/envelope/'>"+
"<message  name='executeQuery'>" +
  "<part name='query' type='xs:string'/>" +
"</message>" +

"<message name='queryResponse'>" +
  "<part name='value' type='xs:string'/>" +
"</message>" +

"<portType name='DINF'>" +
  "<operation name='queryDB'>" +
    "<input message='executeQuery'/>" +
    "<output message='queryResponse'/>" +
  "</operation>" +
"</portType>" +

"<binding type='DINF' name='DINFB'>" +
   "<soap:binding  style='document' " +
   "transport='http://schemas.xmlsoap.org/soap/http' />" +
   "<operation>" +
     "<soap:operation soapAction='http://eulermoz/webServices/queryDB'/>" +
     "<input><soap:body use='literal'/></input>" +
     "<output><soap:body use='literal'/></output>" +
  "</operation>" +
"</binding>" +
        "</definitions>";


function XML2DOM(XMLIn){
    var xmlDoc;
    var parser=new DOMParser();
    try{
        xmlDoc=parser.parseFromString(XMLIn,"text/xml");
    }catch( e) {alert("XML2DOM: cannot parse the XML string!!!\n" + XMLIn);}
    return xmlDoc;
}

function transformToXML(XMLIn){
    var xmlDoc = XML2DOM(XMLIn);
    var processingInstructions = [];
    var done = false;
    var s = "@prefix x: <http://eulermoz/xml#>.\n";
    var stack = [xmlDoc];
    var node;
    var attributes;
    // got to filter out the processing instructions; they are not parsed?
    //writeln("root: " + xmlDoc.getElementsByTagName("note")[0].nodeName);
    //writeln("first child: " + xmlDoc.firstChild.nodeValue);
    while ( stack.length  != 0 ){
        node = stack.shift();
        //writeln("Node type = " + node.nodeType);
        switch (node.nodeType){
           case 1:  // element node
              s = s + "[x:tag '" + node.nodeName + "';x:parent '" +
                node.parentNode.nodeName + "'";
              if (node.hasAttributes()){
                  attributes = node.attributes;
                  for (var k = 0; k < attributes.length; k++){
                      //writeln("attribute == " + attributes[k].nodeName);
                      s = s + ";x:attribute '" + attributes[k].nodeName
                      +"';x:value '" + attributes[k].value + "'";
                  }
              }
              s = s +   "].\n";
              break;
           case 3:   // text node
              s = s +  "[x:text '" + node.nodeValue + "';x:parent '" +
                node.parentNode.nodeName + "'].\n";
              break;
           case 4:   // cdata node
               s = s +  "[x:CDATA '" + node.data + "';x:parent '" +
                 node.parentNode.nodeName + "'].\n";
               break;
           case 6:   // entity node an entity is eg &lt;
                s = s + "[x:ENTITY '" + node.nodeName + "';x:parent '" +
                    node.parentNode.nodeName + "';x:value '" +
                    node.nodeValue + "'].\n";
                break;
           case 7:  // processing instruction
                // processing instructions start with <? and ?>
                // these are not parsed??
                s = s + "[x:PROCESSING_INSTRUCTION '" + node.nodeName + "';x:parent '" +
                    node.parentNode.nodeName + "';x:value '" +
                    node.nodeValue + "'].\n";
                break;
           case 8:  // comment node
                    // between <!-- and -->
                s = s + "[x:COMMENT '" + node.nodeName + "';x:parent '" +
                    node.parentNode.nodeName + "';x:value '" +
                    node.nodeValue + "'].\n";

                //writeln(" type 8:: " + node.nodeName);
                break;
           case 9:  // document node

                //writeln(" type 9: " + node.nodeName + " value " + node.nodeValue);
                break;
           case 10: // document type node
                    // this associates the xml document with a DTD
                //writeln(" type 10: " + node.nodeName);
                s = s + "[x:DOCTYPE '" + node.nodeName + "';x:parent '" +
                    node.parentNode.nodeName + "';x:value '" +
                    node.internalSubset + "'].\n";

                break;
          /* case 11:
                writeln(" type 11: " + node.nodeName);
                break;
           case 12:  // notation node
                     // this permits to add an attribute type to a DTD
                     // example: <!NOTATION GIF SYSTEM "image/gif">
                     // Not detected by parser??
                writeln(" type 12: " + node.nodeName);
                break;*/
           default:
              break;
        }
        for (var i = 0;  i< node.childNodes.length; i++ ){
            stack.push( node.childNodes[i]);
        }
    }
    //writeln("XML: " + s);
    return s;
}

function testE4X(){
    var x = new XML(soapExample1);
    var sp = new Namespace('http://www.w3.org/2001/12/soap-envelope');

    writeln("envelope " + x..sp::Body); // How get the contents???

}

function XMLDomTest(){
    var xmlDoc = XML2DOM(soapExample1);
    writeln(xmlDoc.getElementsByTagName("em:Query")[0]);

}

function getNodeURI(node){
    if (node.nodeType == 1){
        return node.nodeName;
    }
}