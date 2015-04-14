function XmlTree(){

   /* This class defines an xml tree.
    * The tree can have a parent but this is not necessary.
    * Author: Guido J.M. Naudts Bouwel
    */

   // ind gives the horizontal displacement in pretty printing
   var ind = "  ";
   // the alphanumeric content of this tree
   var content = "";
   // the child trees of this tree
   var children = [];
   // the attributes of this tree
   var attributes = [];

   this.init = function(tagName){
      // constructor of an xml tree 
      if (tagName == "Empty"){
         this.type = "Empty";
         this.name = "Empty";
      }else{
         this.type = "Tag";
         this.name = tagName;
         this.children = [];
      }
   } 

   this.addAttribute = function(name, value){
      // add a attribute to the tree
      this.attributes[name] = value;
   }

   this.getAttribute = function(name){
      // get the attribute with name 'name'
      return this.attributes[name];
   } 
         

   this.toStringEmpty = function(tree){
      // transform an empty tree to a string 
      if (tree.type == "Empty")
         return "Empty\n";
   }

   this.toStringXml = function(sep){
      // returns the contents of this xml tree in a string 
      if (this.type == "Empty")
         return "\n";
      else{
         var s = sep + "<" + this.name;
         if (this.attributes.length != 0)
            for (var attrib in this.attributes)
               s = s + " " + attrib + "=" + this.attributes[attrib];
         s = s + ">\n" ;
         if (this.content != "")
            s = s + this.ind + sep + this.content + "\n" ;
         s = s + this.toStringChildren(sep + this.ind);
         return s +  sep + "</" + this.name + ">\n"
      }
   }

   this.toString = function(){
      // returns the contents of this xml tree in a string 
      var sep = " ";
      if (this.type == "Empty")
         return "\n";
      else{
         var s = sep + "<" + this.name;
         if (this.attributes.length != 0)
            for (var attrib in this.attributes)
               s = s + " " + attrib + "=" + this.attributes[attrib];
         s = s + ">\n" ;
         if (this.content != "")
            s = s + this.ind + sep + this.content + "\n" ;
         s = s + this.toStringChildren(sep + this.ind);
         return s +  sep + "</" + this.name + ">\n";
      }
   }  
  
   this.toStringTreeList = function(treeList){
      // returns the contents of this xml treeList in a string 
      var s = "";
      for (var i = 0; i < treeList.length; i++)
         s = s + treeList[i].toStringXml("");
      return s;
   }   

   this.toStringChildren = function(sep){
         // print the children of this xml tree 
         var s = "";
         for (var i = 0; i < this.children.length; i++)
            s = s + this.children[i].toStringXml(sep);
         return s;
   }   

   this.addContent = function(content){
      //  define the content of this tree
      //     or delete it by setting it to ""
      
      this.content = content;
   }

   this.addTree = function(tree){
      // add a tree to the children of this tree 
      this.children = concat(this.children, tree);
   }

   this.addTreeC = function(label, content){
       var t = new XmlTree(label);
       t.addContent(content);
       this.addTree(t);
   }

   this.addTreeP = function(tree){
      /* add a tree to the children of this tree
       * and mark the parent in the child
       */
      tree.setParent(this);
      this.children = concat(this.children, tree);
   }

   this.addTreeList = function(treeList){
      // add a treelist to the children of this tree 
      this.children = concat(this.children + treeList);
   }
      
   this.addTreeListP = function(treeList){
      // add a treelist to the children of this tree
      //    and mark the parent in the children 
      for (var i = 0; i < treeList.length; i++)
         treeList[i].setParent(this);
      this.children = concat(this.children + treeList);
   }

   this.setParent = function(parent){
      // define the parent of this tree 
      this.parent = parent;
   }
   
   this.getChildren = function(){
      // get the children of this tree 
      return this.children;
   }

   this.clearTree = function(){
      // clears the tree 
      this.content = "";
      this.children = [];
   }
   
   this.searchContent = function(treeList, s){
      //  search if there is content that contains a certain string.
      //     input: xml tree list and string; output: bool (0 or 1)
      
      if (treeList.length == 0)
         return 0;
      else{
         if (treeList[0].type != "Empty")
            if (containsString(s, treeList[0].content))
               return 1
         return this.searchContent(subArray(treeList, 1, treeList.length));
      }
   }

   this.getAllTags = function(tree){
      // get a list of all tags in a tree. 
      if (tree.type == "Empty")
         return [];
      else if (tree.children.length == 0)
         return [tree];
      else
         return concat([tree] + this.getAllTagsFromTree(tree.children));
   }

   this.getAllTagsFromTree = function(treeList){
      // get all tags from a treelist 
      if (treeList.length == 0)
         return [];
      else
         return  concat(this.getAllTags(treeList[0]) +
             this.getAllTagsFromTree(subArray(treeList, 1, treeList.length)));
   }

   this.getChildrenByName = function(tree, s){
      /* get all tags from a tree with a given name 
       *  call with outList = []
       */
      if (tree.type == "Empty")
         return [];
      else{
         var list = [];
         var t;
         for (var i = 0; i < tree.children.length; i++){
            t = tree.children[i];
            if (t.name == s)
               list.push[t];
         }
         return list;
      }
   } 

   this.getChildByName = function(s){
      // get the first child with a specific name. 
      if (this.type == "Empty")
         return XmlTree("Empty");
      else{
         var t1 = XmlTree("Empty");
         var t;
         for (var i = 0; i < this.children.length; i++){
            t = this.children[i];
            if (t.name == s){
               t1 = t;
               break;
            }
         }
         return t1;
      }
   }

   this.deleteChildByName = function(s){
      // deletes the first child with a name 
      if (this.type == "Empty")
         return;
      else{
         var copy = [];
         var sw = 0;
         var t;
         for (var i = 0; i < this.children.length; i++){
            t = this.children[i];
            if (t.name == s && sw == 0)
               sw = 1;
            else
               copy.push(t);
         }
         this.children = copy;
         return;
      }
   }

   this.deleteAllChildren = function(s){
      // delete all children with a specific name 
      if (this.type == "Empty")
         return;
      else{
         var copy = [];
         var t;
         for (var i = 0; i < this.children.length; i++){
            t = this.children[i];
            if (t.name != s)
               copy.push(t);
         }
         this.children = copy;
         return; 
      }
   } 
      
   this.getDirectChildrenByName = function(s){
      /* get all tags with a given name that directly descend
       *   from the given tag.
       */
      if (this.type == "Empty")
         return [];
      else{
         var copy = [];
         var t;
         for (var i = 0; i < this.children.length; i++){
            t = this.children[i];
            if (t.name == s)
               copy.push(t);
         }
         return copy;
      }
   }   
      
   this.walkATree = function(tree, f){
      /*  walk a tree. The first input is the tree to walk.
       *  The second input is a function f with signature f(XmlTree)
       *  that takes as input an XML tree and as output an XML tree.
       *  This function normally changes the tagname or content of the tree.
       *  Recursively it will be applied to all children of the tree.
       *  The output tree of walkATree is the modified input tree.
       */
      var tree1 = f(tree);
      if (tree1 != undefined){
         tree = tree1;
         if (tree.children.length != 0)
            tree.children = this.walkAList(tree.children, object);
      }
      return tree;
   }

   this.walkAList = function(treeList, f){
      // apply a function f to each element of a tree list 
      if (treeList.length == 0)
         return [];
      else
         return [this.walkATree(treeList[0], f)]
                 + this.walkAList(subArray(treeList, 1, treeList.length), f);
   }

   this.selectFromTree = function(tree, f){
    /* select tags from a tree. The first input is the tree to select from.
     * The second input is a function f
     * that takes as input an XML tree and as output an XML Tree.
     * This function is applied to every tag of the input tree and
     * must return the Tag or an Empty tag (xml.XmlTree("Empty").
     * The output tree is the concatenation of
     * the output from this function.
     * Only non empty tags will be returned in a tree list.
     */
     var tag = f(tree);
     treeList = [];
     if (tag != undefined)
         treeList.push(tag);
     tagList = this.selectFromList(tree.children, f);
     return concat(treeList, tagList);
   }  

   this.selectFromList = function(treeList, f){
      /* apply a function f from an object to each element of a tree list
       * accumulate the tags returned by f and return a tree list.
       */
      if (treeList.length == 0)
         return [];
      else
         return (concat(this.selectFromTree(treeList[0], f) +
                           this.selectFromList(subArray(treeList, 1, treeList.length))), f);
   } 

   this.eliminateEmpties = function(treeList){
      //  eliminate all empty trees 
      var list = [];
      var tree; 
      for (var i = 0; i < treeList.length; i++){
          tree = treeList[i];
          if (tree.type != "Empty")
             list.push(tree);
      }
      return list;
   }          

   this.createEmpty = function(){
      // create empty tree  
      return new XmlTree("Empty");
   }

   this.compareTrees = function(tree1, tree2){
      /* compare two trees
       * this compares only name and content
       */
      if (tree1.name == tree2.name)
         if (tree.content == tree2.content)
               return 1;
         else
            return 0;
      else
         return 0;
   }

   this.compareTreesFull = function(tree1, tree2){
      /* compare two trees
       * this compares name, content and children
       */
      if (tree1.name == tree2.name)
         if (tree.content == tree2.content){
            var children1 = tree1.children;
            var children2 = tree2.children;
            var flag = 0;
            for (var t1 = 0; t1 < children1.length; t1++){
               flag = 0;
               for (var t2 = 0; t2 < children2.length; t2++)
                  if (this.compareTreesFull(children1[t1], children2[t2])){
                     flag = 1;
                     break;
                  } 
               if (flag == 0)
                  return 0;
            }
            return 1;
         }else
            return 0;
      else
         return 0;
   }

   this.copy = function(){
      // copy this tree 
      var tree = new XmlTree(this.name);
      tree.content = this.content;
      for (var i = 0; i < this.children.length; i++)
         tree.addTree(this.children[i].copy());
      return tree;
   }

   this.replaceChild = function(tree, name){
      // replace the first child with the given name by the given tree. 
      var l = [];
      var t; 
      for (var i = 0; i < this.children.lenth; i++){
         t = this.children[i]; 
         if (t.name == name)
            l.push(tree);
         else
            l.push(t);
      }
      this.children = l; 
    }
    
   this.isEmpty = function(){
        if (this.name == "Empty")
            return 1;
        else
            return 0;
   }
 
   this.compare = function(triple){
        return this.compareTreesFull(triple);
   }

   this.toFile = function(filename){ 
   // needs interface.js
       saveAFile(filename, this.toString());
   }

   this.toStringTreeList = function(treeList){
   /* returns the contents of this xml treeList in a string */
     var s = ""
     for (var i = 0; i < treeList.length; i++)
       s = s + treeList[i].toStringXml("");
     return s;
   } 
   
}
