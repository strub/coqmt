(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: undo_lablgtk_lt26.mli 13323 2010-07-24 15:57:30Z herbelin $ i*)

(* An undoable view class *)

class undoable_view : Gtk.text_view Gtk.obj ->
object
  inherit GText.view
  method undo : bool
  method redo : bool
  method clear_undo : unit
end

val undoable_view :
    ?buffer:GText.buffer ->
    ?editable:bool ->
    ?cursor_visible:bool ->
    ?justification:GtkEnums.justification ->
    ?wrap_mode:GtkEnums.wrap_mode ->
    ?border_width:int ->
    ?width:int ->
    ?height:int ->
    ?packing:(GObj.widget -> unit) ->
    ?show:bool ->
    unit ->
  undoable_view


