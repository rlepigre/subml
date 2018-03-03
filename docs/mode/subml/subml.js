(function(mod) {
  if (typeof exports == "object" && typeof module == "object") // CommonJS
    mod(require("../../lib/codemirror"));
  else if (typeof define == "function" && define.amd) // AMD
    define(["../../lib/codemirror"], mod);
  else // Plain browser env
    mod(CodeMirror);
})(function(CodeMirror) {
"use strict";

CodeMirror.defineMode("subml", function(_config, modeConfig) {

  function switchState(source, setState, f) {
    setState(f);
    return f(source, setState);
  }

  var smallRE = /[a-z_]/;
  var largeRE = /[A-Z]/;
  var greekRE = /\u03B1|\u03B2|\u03B3|\u03B4/;
  var idRE    = /[a-z_'A-Z0-9]/;
  var intRE   = /[0-9]/;
  var whiteRE = /[ \t\v\f]/; // newlines are handled in tokenizer

  function normal(source, setState) {
    if (source.eatWhile(whiteRE)) {
      return null;
    }

    var ch = source.next();

    // Handling of comments.
    if (ch == '(' && source.eat('*')) {
      return switchState(source, setState, ncomment("comment", 1));
    }

    // Handling of string literals.
    if (ch == '"') {
      return switchState(source, setState, stringLiteral);
    }

    // Handling of macros
    if (ch == '\\') {
      source.eatWhile(/[a-zA-Z]/);
      if (source.eol()) return "special";
      return "error";
    }

    if (ch == '*' && source.eol()) {
      return "special";
    }

    if (ch == '-' && source.eat('>') && source.eol()) {
      return "special";
    }

    // Handling of variables and constructors.
    if (largeRE.test(ch)) {
      source.eatWhile(idRE);
      return "variable-2";
    }

    if (greekRE.test(ch)){
      source.eatWhile(whiteRE);
      if (source.eat('+')) {
        source.eatWhile(whiteRE);
        source.eatWhile(intRE);
      }
      return "variable-2";
    }

    if (smallRE.test(ch)) {
      source.eatWhile(idRE);
      return "variable";
    }

    // Default to error.
    return "error";
  }

  function ncomment(type, nest) {
    if (nest == 0) {
      return normal;
    }
    return function(source, setState) {
      var currNest = nest;
      while (!source.eol()) {
        var ch = source.next();
        if (ch == '(' && source.eat('*')) {
          ++currNest;
        }
        else if (ch == '*' && source.eat(')')) {
          --currNest;
          if (currNest == 0) {
            setState(normal);
            return type;
          }
        }
      }
      setState(ncomment(type, currNest));
      return type;
    };
  }

  function stringLiteral(source, setState) {
    while (!source.eol()) {
      var ch = source.next();
      if (ch == '"') {
        setState(normal);
        return "string";
      }
      if (ch == '\\') {
        var ch = source.next();
        if (ch != '\\' && ch != 'n' && ch != 't'){
          return "error";
        }
      }
    }
    setState(normal);
    return "error";
  }

  var wellKnownWords = (function() {
    var wkw = {};
    function setType(t) {
      return function () {
        for (var i = 0; i < arguments.length; i++)
          wkw[arguments[i]] = t;
      };
    }

    setType("keyword")(
      "type", "fun", "val", "case", "of", "include", "fix", "check", "eval",
      "if", "then", "else", "with", "rec", "let", "in", "such", "that",
      "abort"
    );

    setType("builtin")(
      "=", ";", ":", ".", "{", "}", "(", ")", ",", "[", "]", "|",
      "\u03BB" /* lambda */, "\u03BC" /* mu */, "\u03BD" /* nu */,
      "\u2200" /* forall */, "\u2203" /* exists */, "\u2192" /* arrow */,
      "\u00d7" /* times */, "\u2286" /* subseteq */, "\u03B5" /* epsilon */,
      "\u221E" /* infinity */, "\u2026" /* elipsis */
    );

    var override = modeConfig.overrideKeywords;
    if (override) for (var word in override) if (override.hasOwnProperty(word))
      wkw[word] = override[word];

    return wkw;
  })();



  return {
    startState: function ()  { return { f: normal }; },
    copyState:  function (s) { return { f: s.f }; },

    token: function(stream, state) {
      var t = state.f(stream, function(s) { state.f = s; });
      var w = stream.current();
      return wellKnownWords.hasOwnProperty(w) ? wellKnownWords[w] : t;
    },

    blockCommentStart: "(*",
    blockCommentEnd: "*)"
  };

});

CodeMirror.defineMIME("text/x-subml", "subml");

});
