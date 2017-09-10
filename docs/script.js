var edit = undefined;
var term = undefined;
var prelude = false;

function loadsubmlfile(fn) {
  if (fn == "tutorial.typ") dir = "subml/";
  else dir = "subml/lib/";
  $.ajax({
    type     : "GET",
    url      : dir + fn,
    dataType : 'text',
    success  :
      function (data) {
	  edit.setValue(data);
    }
  });
}

var worker = new Worker ("main.js")

function evalsubmlfile(fn,cont) {
  $.ajax({
    url      : "subml/" + fn,
    dataType : 'text',
    success  :
      function (data) {
          ASYNCH (fn, data, function (resp) { cont(resp); })
      }
  });
}

$(function() {
  // Creation of editors.
  edit = CodeMirror(document.getElementById("edit"), {
    lineNumbers    : true,
    lineWrapping   : true,
    theme          : "solarized",
    scrollbarStyle : "simple",
    extraKeys      : {
      // Tabs changed into spaces.
      Tab :
        function(instance){
          var spaces = Array(instance.getOption("indentUnit") + 1).join(" ");
          instance.replaceSelection(spaces);
        },
      Space :
        function(instance){
          var pos = instance.getCursor();
          var line = instance.getLine(pos.line);
          line = line.substring(0, pos.ch);
          if(line.length == 0 || line.charAt(line.length - 1) == ' '){
            instance.replaceSelection(" ");
          } else {
            var last = line.length - 1;
            while(last > 0 && line.charAt(last - 1) != ' '){
              last = last - 1;
            }
            switch (line.substring(last, line.length)) {
              case "->" :
              case "\\to" :
                instance.setSelection({line : pos.line, ch : last}, pos);
                instance.replaceSelection("\u2192 ");
                break;
              case "|->" :
              case "\\mapsto" :
                instance.setSelection({line : pos.line, ch : last}, pos);
                instance.replaceSelection("\u21A6 ");
                break;
              case "forall" :
              case "\\forall" :
              case "/\\" :
                instance.setSelection({line : pos.line, ch : last}, pos);
                instance.replaceSelection("\u2200");
                break;
              case "exists" :
              case "\\exists" :
              case "\\/" :
                instance.setSelection({line : pos.line, ch : last}, pos);
                instance.replaceSelection("\u2203");
                break;
              case "\\lambda" :
              case "\\" :
                instance.setSelection({line : pos.line, ch : last}, pos);
                instance.replaceSelection("\u03BB");
                break;
              case "\\Lambda" :
                instance.setSelection({line : pos.line, ch : last}, pos);
                instance.replaceSelection("\u039B");
                break;
              case "\\mu" :
              case "!" :
                instance.setSelection({line : pos.line, ch : last}, pos);
                instance.replaceSelection("\u03BC");
                break;
              case "\\nu" :
              case "?" :
                instance.setSelection({line : pos.line, ch : last}, pos);
                instance.replaceSelection("\u03BD");
                break;
              case "\\subset" :
              case "<" :
                instance.setSelection({line : pos.line, ch : last}, pos);
                instance.replaceSelection("\u2282 ");
                break;
              case "*" :
                instance.setSelection({line : pos.line, ch : last}, pos);
                instance.replaceSelection("\u00D7 ");
                break;
              case "\\alpha" :
                instance.setSelection({line : pos.line, ch : last}, pos);
                instance.replaceSelection("\u03B1 ");
                break;
              case "\\beta" :
                instance.setSelection({line : pos.line, ch : last}, pos);
                instance.replaceSelection("\u03B2 ");
                break;
              case "\\gamma" :
                instance.setSelection({line : pos.line, ch : last}, pos);
                instance.replaceSelection("\u03B3 ");
                break;
              case "\\delta" :
                instance.setSelection({line : pos.line, ch : last}, pos);
                instance.replaceSelection("\u03B4 ");
                break;
              case "\\epsilon" :
                instance.setSelection({line : pos.line, ch : last}, pos);
                instance.replaceSelection("\u03B5 ");
                break;
              default :
                instance.replaceSelection(" ");
            }
          }
        },
    }
  });

  edit.on('cursorActivity',
    function(instance){
      var pos = instance.getCursor();
      $( "#pos" ).text((pos.line+1)+','+pos.ch);
    });

  term = CodeMirror(document.getElementById("term"), {
    lineWrapping   : true,
    readOnly       : "nocursor",
    theme          : "solarized",
    scrollbarStyle : "simple"
  });

  // Loading default file in the editor.
  loadsubmlfile("tutorial.typ");

  // Making things resizable.
  $( "#west" ).resizable({
    handles  : "e",
    minWidth : 400,
    maxWidth : (document.body.clientWidth - 400)
  });

  $( "#edit" ).resizable({
    handles    : "s",
    minHeight  : 100,
    maxHeight  : (document.body.clientHeight - 120),
    resize     :
      function( event, ui ) {
        $( "#term" ).css("height", "calc(100% - "+ui.size.height+"px - 3ex)");
        term.refresh();
        edit.refresh();
      }
  });
});


var worker_handler = new Object ();

function add_to_term(s) {
    var doc = term.getDoc();
    var cursor = doc.getCursor(); // gets the line number in the cursor position
    var line = doc.getLine(cursor.line); // get the line contents
    if (line.length > 0) { cursor.ch = line.length; }
    doc.replaceRange(s, cursor); // adds a new line
}

worker.onmessage =
    function (m) {
	if (m.data.typ != 'result') {
	    add_to_term(m.data.result);
	} else {
	    console.log("[ASYNCH] back from " + m.data.fname);
	    add_to_term(m.data.result);
	}
    }

function ASYNCH (action_name, action_args, cont) {
  worker_handler[action_name] = cont;
  worker.postMessage ({fname: action_name, args: action_args});
  console.log ("[ASYNCH] " + action_name);
}

function subml_eval() {
    var s = edit.getValue();
    ASYNCH ("editor", s, function (resp) { add_to_term(resp); });
}
