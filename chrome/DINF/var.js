const _NS_RDF               = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
const _NS_RDFS              = "http://www.w3.org/2000/01/rdf-schema#";
const _NS_XUL               = "http://www.mozilla.org/keymaster/gatekeeper/there.is.only.xul"
const _NS_RULES             = "http://www.ptb.org/prolog#";
const _NS_CLERK             = "http://www.vicertec.org/rdfs/clerk.rdfs#";

netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
const JS_FILE_IOSERVICE_CID    = "@mozilla.org/network/io-service;1";
const JS_FILE_I_STREAM_CID     = "@mozilla.org/scriptableinputstream;1";
const JS_FILE_OUTSTREAM_CID    = "@mozilla.org/network/file-output-stream;1";

const JS_FILE_F_TRANSPORT_SERVICE_CID  = "@mozilla.org/network/file-transport-service;1";

const JS_FILE_I_IOSERVICE              = Components.interfaces.nsIIOService;
const JS_FILE_I_SCRIPTABLE_IN_STREAM   = "nsIScriptableInputStream";
const JS_FILE_I_FILE_OUT_STREAM        = Components.interfaces.nsIFileOutputStream;

const JS_FILE_InputStream  = new Components.Constructor(JS_FILE_I_STREAM_CID, JS_FILE_I_SCRIPTABLE_IN_STREAM);

const JS_FILE_IOSERVICE    = Components.classes[JS_FILE_IOSERVICE_CID].getService(JS_FILE_I_IOSERVICE);

const JS_FILE_NS_RDONLY               = 0x01;
const JS_FILE_NS_WRONLY               = 0x02;
const JS_FILE_NS_RDWR                 = 0x04;
const JS_FILE_NS_CREATE_FILE          = 0x08;
const JS_FILE_NS_APPEND               = 0x10;
const JS_FILE_NS_TRUNCATE             = 0x20;
const JS_FILE_NS_SYNC                 = 0x40;
const JS_FILE_NS_EXCL                 = 0x80;
const JS_FILE_FILE_TYPE     = 0x00;
const JS_FILE_DEFAULT_PERMS = 0644;
const JS_FS_LOCAL_CID      = "@mozilla.org/file/local;1";
const JS_FS_I_LOCAL_FILE   = "nsILocalFile";
const JS_FS_INIT_W_PATH    = "initWithPath";

const JS_FS_File_Path      = new Components.Constructor
  (JS_FS_LOCAL_CID, JS_FS_I_LOCAL_FILE, JS_FS_INIT_W_PATH);

var	container   = window;
var	application = window;
