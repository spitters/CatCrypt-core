/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import VersoManual
import CoreManual

open Verso Doc
open Verso.Genre Manual

/-- Single-page (`file://`) navigation: on the `html-single` build, drops verso's
    relative `<base>` so links and assets resolve against the document, and routes
    `find/?…` cross-references to their in-page target. -/
def navFixJs : String :=
r#"(function () {
  if (!/\/html-single\//.test(location.pathname)) return;
  try { var b = document.querySelector('base'); if (b && b.parentNode) b.parentNode.removeChild(b); } catch (e) {}
  document.addEventListener('click', function (e) {
    var t = e.target;
    var a = (t && t.closest) ? t.closest('a') : null;
    if (!a) return;
    var h = a.getAttribute('href') || '';
    var q = h.indexOf('find/?');
    if (q === -1) return;
    var id;
    try { id = new URLSearchParams(h.slice(h.indexOf('?'))).get('name') || ''; } catch (e2) { id = ''; }
    if (!id) return;
    var el = document.getElementById(id);
    if (!el) return;
    e.preventDefault();
    el.scrollIntoView();
    try { history.replaceState(null, '', '#' + id); } catch (e3) {}
  }, false);
})();"#

/-- The nav-fix script, injected into every page's `<head>` via `extraHead`. -/
def navFixHead : Output.Html := .tag "script" #[] (.text false navFixJs)

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .immediately
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraHead := #[navFixHead]

def main := manualMain (%doc CoreManual) (config := config)
