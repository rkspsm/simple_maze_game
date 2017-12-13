package maze ;

import kotlin.js.* ;
import kotlin.browser.* ;
import org.w3c.dom.Window ;
import org.w3c.dom.Document ;
import kotlin.collections.MutableSet ;
import kotlin.collections.MutableList ;

// ------------- Module Helpers. -------------------

fun Any?._discard () = Unit ;

fun current_time () : Double { return js ("Date.now ()") ; }
fun sched (ms : Double, fn : () -> Unit) = window.setTimeout (fn, ms.toInt ()) ;
fun sched (ms : Int, fn : () -> Unit) = window.setTimeout (fn, ms) ;

@JsName ("Array")
external class js_array constructor (_data : Any?) { }

@JsName ("Blob")
external open class blob constructor (_data : js_array, _type : Json) {
  @JsName ("type")
  val mime_type : String ;

}

fun blob.is_json () : Boolean =
  this.mime_type == "application/json" ;

fun json_blob (stuff : Json) : blob = blob (
  js_array (JSON.stringify (stuff)) ,
  json (Pair ("type", "application/json"))) ;


external interface url_interface {

  @JsName ("createObjectURL")
  fun create_object_url (d : blob) : String ;

}

@JsName ("URL")
external val url : url_interface ;

fun json_download_url (x : Json) : String =
  url.create_object_url (json_blob (x)) ;

@JsName ("File")
external class file_interface : blob {

  val size : Double ;
}

@JsName ("FileReader")
external class file_reader {

  @JsName ("addEventListener")
  fun add_event_listener (e : String, fn : () -> Unit) : Unit ;

  @JsName ("readAsText")
  fun read_as_text (x : file_interface) : Unit ;

  @JsName ("result")
  val string_result : String ;
}

fun file_reader.read_text_file (f : file_interface, fn : (String) -> Unit) : Unit {
  this.add_event_listener ("loadend", { fn (this.string_result) }) ;
  this.read_as_text (f) ;
}

external interface file_list {
  val length : Int ;

  fun item (x : Int) : file_interface
}

external interface data_transfer {
  val files : file_list ;
}

external interface original_event {
  @JsName ("dataTransfer")
  val data_transfer : data_transfer ;
}

external interface jquery {

  interface event {
    @JsName ("originalEvent")
    val original_event : original_event ;

    @JsName ("preventDefault")
    fun prevent_default () : Unit ;

    @JsName ("stopPropagation")
    fun stop_propagation () : Unit ;

    val which : Int ;
  }

  @JsName ("addClass")
  fun add_class (x : String) : jquery ;
  fun append (x : jquery) : jquery ;
  @JsName ("appendTo")
  fun append_to (x : jquery) : jquery ;
  fun attr (x : String, y : String) : jquery ;

  fun <T> prop (x : String) : T ;
  fun <T> prop (x : String, v : T) : jquery ;
  fun children (x : String = definedExternally) : jquery ;
  @JsName ("click")
  fun on_click (fn : (evt: event) -> Unit) : jquery ;
  fun css (k : String, v : String) : jquery ;

  fun eq (x : Int) : jquery ;

  fun find (x : String) : jquery ;

  fun hide () : jquery ;

  @JsName ("innerHeight")
  fun inner_height (x : Double) : jquery ;
  @JsName ("innerHeight")
  fun inner_height () : Double ;
  @JsName ("innerWidth")
  fun inner_width (x : Double) : jquery ;
  @JsName ("innerWidth")
  fun inner_width () : Double ;

  @JsName ("keydown")
  fun on_keydown (fn : (evt: event) -> Unit): jquery ;
  @JsName ("keyup")
  fun on_keyup (fn : (evt: event) -> Unit) : jquery ;

  fun on (x : String, fn : (event) -> Unit) : jquery ;

  fun prepend (x : jquery) : jquery ;
  @JsName ("prependTo")
  fun prepend_to (x : jquery) : jquery ;

  fun remove () : jquery ;

  fun show () : jquery ;

  fun text (x : String) : jquery ;

  @JsName ("val")
  fun value () : String ;
  @JsName ("val")
  fun value (x : String) : jquery ;
}

external fun jQuery (x : String = definedExternally) : jquery ;
external fun jQuery (x : Window) : jquery ;
external fun jQuery (x : Document) : jquery ;

fun jquery.checked () : Boolean = this.prop<Boolean> ("checked") ;
fun jquery.checked (bv : Boolean) : jquery =
  this.prop<Boolean> ("checked", bv) ;

fun jquery.on_load (fn : (jquery.event) -> Unit) : jquery 
  = this.on ("load", fn) ;

fun span_label (v:String = "") : jquery =
  jQuery ("<span></span>").text (v) ;

fun div_label (v:String = "") : jquery =
  empty_div ().text (v) ;

fun html_input (t:String = "text") : jquery =
  jQuery ("<input>").attr ("type", t) ;

fun empty_div () : jquery =
  jQuery ("<div></div>") ;

fun empty_button () : jquery =
  jQuery ("<button></button>") ;

fun ahref () : jquery {
  val e = jQuery ("<a></a>") 
    .attr ("href", "#")
  ;

  e.on_click ({ evt ->
    evt.prevent_default () ;
    evt.stop_propagation () ;
  }) ;
  return e ;
}

fun unordered_list () : jquery = jQuery ("<ul></ul>") ;
fun list_item () : jquery = jQuery ("<li></li>") ;
fun br () : jquery = jQuery ("<br>") ;
fun hr () : jquery = jQuery ("<hr>") ;
fun table () : jquery = jQuery ("<table></table>")
  .attr ("cellspacing", "0")
  .attr ("cellpadding", "0") ;
fun table_head () : jquery = jQuery ("<thead></thead>") ;
fun table_body () : jquery = jQuery ("<tbody></tbody>") ;
fun table_row () : jquery = jQuery ("<tr></tr>") ;
fun table_data () : jquery = jQuery ("<td></td>") ;

external interface Ramda {

  @JsName ("defaultTo")
  fun <T> default_to (t : T, x : Any?) : T ;

  @JsName ("isNil")
  fun is_nil (x : Any?) : Boolean ;
}

external val R : Ramda ;

external fun parseInt (x : String) : Any? ;
external fun parseFloat (x : String) : Any? ;

fun as_int (df : Int, x : String) : Int {
  return R.default_to<Int> (df, parseInt (x)) ;
}

fun as_double (df : Double, x : String) : Double {
  return R.default_to<Double> (df, parseFloat (x)) ;
}

fun ok_dialog (msg : String, _extra : jquery? = null) : Unit {
  val extra = _extra ?: empty_div () ;

  jQuery (".main").hide () ;

  val dialog = empty_div ()
    .css ("position", "absolute")
    .css ("top", "0px")
    .css ("bottom", "0px")
    .css ("z-index", "300")
    .css ("opacity", "1")
    .css ("background-color", "white")
    .append (empty_div ().text (msg))
    .append (extra)
  ;

  dialog
    .append (empty_button ()
      .text ("Ok")
      .on_click ({ _ -> jQuery (".main").show () ; dialog.remove () }))
    .on ("dragover drop", { evt -> evt.stop_propagation () })
    .inner_width (jQuery (window).inner_width ())
    .inner_height (jQuery (window).inner_height ())
    .prepend_to (jQuery ("body"))
}

// ------------------ End Helpers. ------------------

typealias is_opened = Boolean ;
val is_opened_true = true ;
val is_opened_false = false ;

sealed class location ;
object loc_empty : location () ;
object loc_player : location () ;
object loc_wall : location () ;
object loc_key : location () ;
data class loc_door (val opened : is_opened) : location () ;

typealias loc_map = MutableList<MutableList<location>> ;

fun copy_loc_map (l : loc_map) : loc_map {
  val result : loc_map = mutableListOf () ;
  for (lr in l) {
    val row : MutableList<location> = mutableListOf () ;
    row.addAll (lr) ;
    result.add (row) ;
  }
  return result ;
}

fun loc_map_count (lm : loc_map, l : location) : Int {
  var result = 0 ;
  for (lr in lm) {
    for (l_ in lr) {
      if (l_ == l) {
        result += 1 ;
      }
    }
  }

  return result ;
}

fun board_find (board : loc_map, l : location) : coords {
  for ((row, lr) in board.withIndex ()) {
    for ((col, l_) in lr.withIndex ()) {
      if (l_ == l) {
        return coords (row, col) ;
      }
    }
  }

  return coords (0, 0) ;
}

fun loc_map_valid (lm : loc_map) : Boolean {
  var c1 : Boolean ; 
  if (lm.size == 0) { c1 = true; }
  else {
    val sz = lm[0].size ;
    c1 = true ;
    for (lr_ in lm) {
      if (lr_.size != sz) {
        c1 = false ;
        break ;
      }
    }
  }

  val c2 = loc_map_count (lm, loc_player) == 1 ;
  val c3 = 1 <= (
    loc_map_count (lm, loc_door (is_opened_true)) +
    loc_map_count (lm, loc_door (is_opened_false))) ;

  return c1 && c2 && c3 ;
}

sealed class major_ui ;
object ui_game : major_ui () ;
object ui_postgame : major_ui () ;
object ui_menu : major_ui () ;
object ui_designer : major_ui () ;
object ui_replay : major_ui () ;

typealias is_victorious = Boolean ;
typealias is_paused = Boolean ;

val is_paused_true = true ;
val is_paused_false = false ;
val is_victorious_true = true ;
val is_victorious_false = false ;

sealed class app_state ;
object appst_launched : app_state () ;
data class appst_game (val paused : is_paused) : app_state () ;
data class appst_postgame (val is_vict : is_victorious) : app_state () ;
object appst_menu : app_state () ;
object appst_designer : app_state () ;
object appst_replay : app_state () ;

sealed class timer_control ;
object tc_reset : timer_control () ;
object tc_run : timer_control () ;
object tc_stop : timer_control () ;
object tc_pause : timer_control () ;

data class coords (var row : Int = 0, var col : Int = 0) ;

sealed class movement ;
object mv_up : movement () ;
object mv_left : movement () ;
object mv_right : movement () ;
object mv_down : movement () ;

typealias game_time = Double ;
typealias start_time = Double ;

data class game_fuel (var remaining : Int) ;

typealias location_update = Pair<coords, location> ;
typealias location_updates = Array<location_update> ;

sealed class move_command ;
data class mvcmd_update_coords (val c : coords, val l : location) : move_command () ;
object mvcmd_key_update_doors : move_command () ;
object mvcmd_trigger_victory : move_command () ;
object mvcmd_expend_fuel : move_command () ;
data class mvcmd_update_player_coords (val c : coords) : move_command () ;
data class mvcmd_append_to_replay (val lups : location_updates) : move_command () ;
data class mvcmd_add_fuel (val c : coords) : move_command () ;

class process_move constructor
  (val mrow : Int, val mcol : Int, val board : loc_map, val src : coords) {

  fun move_within_bounds (m : movement) : coords? {
    return when (m) {
      is mv_up -> if (src.row == 0) null else src.copy (row = src.row - 1)
      is mv_down -> if (src.row == mrow) null else src.copy (row = src.row + 1)
      is mv_left -> if (src.col == 0) null else src.copy (col = src.col - 1)
      is mv_right -> if (src.col == mcol) null else src.copy (col = src.col + 1)
    }
  }

  fun map_location (c : coords) : location = 
    board[c.row][c.col] ;

  operator fun invoke (mv : movement) : Array<move_command> {
    val _dest : coords? = move_within_bounds (mv) ;
    _dest?.let {
      val loc = map_location (_dest) ;
      return when (loc) {
        is loc_empty -> arrayOf (
          mvcmd_update_coords (src, loc_empty),
          mvcmd_update_coords (_dest, loc_player),
          mvcmd_update_player_coords (_dest),
          mvcmd_expend_fuel,
          mvcmd_append_to_replay (arrayOf (
            Pair (src, loc_empty), Pair (_dest, loc_player)))
        )
        is loc_key -> arrayOf (
          mvcmd_update_coords (src, loc_empty),
          mvcmd_update_coords (_dest, loc_player),
          mvcmd_update_player_coords (_dest),
          mvcmd_key_update_doors,
          mvcmd_add_fuel (_dest),
          mvcmd_append_to_replay (arrayOf (
            Pair (src, loc_empty), Pair (_dest, loc_player)))
        )
        is loc_door -> when (loc.opened) {
          false -> arrayOf ()
          true -> arrayOf (
            mvcmd_update_coords (src, loc_empty),
            mvcmd_update_coords (_dest, loc_player),
            mvcmd_update_player_coords (_dest),
            mvcmd_append_to_replay (arrayOf (
              Pair (src, loc_empty), Pair (_dest, loc_player))) ,
            mvcmd_trigger_victory
          )
        }
        else -> arrayOf ()
      }
    }

    return arrayOf () ;
  }

}

sealed class replay_command ;
data class rcmd_init (val gt : game_time) : replay_command () ;
data class rcmd_loc_update 
  (val gt : game_time, val lups : location_updates) : replay_command () ;
data class rcmd_fuel_update
  (val gt : game_time, val fuel : game_fuel) : replay_command () ;
data class rcmd_finish
  (val gt : game_time, val is_vict : is_victorious) : replay_command () ;
data class rcmd_abort (val gt : game_time) : replay_command () ;

class replay_context constructor (
  val fuel : game_fuel,
  val st : start_time)
{
  val gt : game_time
    get () = current_time () ;

  fun relproc_move_replay (cmd : move_command) : Array<replay_command> {
    return when (cmd) {
      is mvcmd_append_to_replay -> arrayOf (
        rcmd_fuel_update (gt, fuel.copy ()) ,
        rcmd_loc_update (gt, cmd.lups)
      )
      else -> arrayOf ()
    }
  }

  fun relproc_replay (cmd : command) : Array<replay_command> {
    return when (cmd) {
      is cmd_game_init_replay -> arrayOf (rcmd_init (gt))
      is cmd_game_finish_replay -> cmd.is_vict?.let {
        when (cmd.is_vict) {
          true -> arrayOf<replay_command> (rcmd_finish (gt, is_victorious_true))
          false -> arrayOf<replay_command> (rcmd_finish (gt, is_victorious_false))
        }
      } ?: arrayOf<replay_command> (rcmd_abort (gt))
      else -> arrayOf ()
    }
  }
}

typealias level_index = Int ;

sealed class stimulus ;

object stls_launched : stimulus () ;

object stls_menu_levels_fetched : stimulus () ;
data class stls_menu_level_selected (val li : level_index) : stimulus () ;
object stls_menu_designer : stimulus () ;
object stls_menu_replay : stimulus () ;
object stls_menu_game_info : stimulus () ;
object stls_back_from_designer : stimulus () ;

data class stls_game_moved (val m : movement) : stimulus () ;
object stls_game_tick : stimulus () ;
data class stls_game_pause (val pause : Boolean) : stimulus () ;
object stls_game_quit : stimulus () ;
object stls_game_victory : stimulus () ;
object stls_game_fuel_empty : stimulus () ;

object stls_postgame_goto_menu : stimulus () ;
object stls_postgame_play_again : stimulus () ;
object stls_postgame_download_replay : stimulus () ;

sealed class command ;

data class cmd_set_state (val state : app_state) : command () ;
data class cmd_select_ui (val ui : major_ui) : command () ;
object cmd_setup_ui : command () ;

object cmd_menu_fetch_builtin_levels : command () ;
object cmd_menu_populate : command () ;
data class cmd_menu_select_level (val li : level_index) : command () ;

data class cmd_game_timer (val tc : timer_control) : command () ;
data class cmd_game_pause (val pause : Boolean) : command () ;
object cmd_game_fuel_tick : command () ;
data class cmd_game_process_move (val m : movement) : command () ;
object cmd_game_init_replay : command () ;
data class cmd_game_finish_replay (val is_vict : is_victorious?) : command () ;

object cmd_postgame_reset_map : command () ;
data class cmd_postgame_set_theme (val is_vict : is_victorious) : command () ;
object cmd_postgame_prepare_replay : command () ;
object cmd_postgame_offer_replay_download : command () ;
object cmd_transfer_to_designer : command () ;

fun process (ast : app_state, stim : stimulus) : Array<command> {

  return when (ast) {

    is appst_launched -> when (stim) {
      is stls_launched -> arrayOf (
        cmd_setup_ui ,
        cmd_set_state (appst_menu) ,
        cmd_select_ui (ui_menu) ,
        cmd_menu_fetch_builtin_levels )
      else -> arrayOf ()
    }

    is appst_menu -> when (stim) {
      is stls_menu_levels_fetched -> arrayOf<command> (
          cmd_menu_populate )
      is stls_menu_level_selected -> arrayOf (
        cmd_menu_select_level (stim.li) ,
        cmd_select_ui (ui_game) ,
        cmd_game_timer (tc_reset) ,
        cmd_game_timer (tc_run) ,
        cmd_set_state (appst_game (false)) ,
        cmd_game_init_replay
      )
      is stls_menu_designer -> arrayOf (
        cmd_set_state (appst_designer) ,
        cmd_select_ui (ui_designer) ,
        cmd_transfer_to_designer )

      else -> arrayOf ()
    }

    is appst_game -> when (ast.paused) {
      false -> when (stim) {
        is stls_game_tick -> arrayOf<command> (cmd_game_fuel_tick)
        is stls_game_pause -> when (stim.pause) {
          true -> arrayOf (
            cmd_game_timer (tc_pause) ,
            cmd_set_state (appst_game (is_paused_true)))
          false -> arrayOf ()
        }
        is stls_game_moved -> arrayOf<command> (
          cmd_game_process_move (stim.m))
        is stls_game_victory -> arrayOf (
          cmd_set_state (appst_postgame (is_victorious_true)) ,
          cmd_game_finish_replay (is_victorious_true) ,
          cmd_game_timer (tc_stop) ,
          cmd_postgame_set_theme (is_victorious_true) ,
          cmd_select_ui (ui_postgame) ,
          cmd_postgame_prepare_replay
        )
        is stls_game_fuel_empty -> arrayOf (
          cmd_set_state (appst_postgame (is_victorious_false)) ,
          cmd_game_finish_replay (is_victorious_false) ,
          cmd_game_timer (tc_stop) ,
          cmd_postgame_set_theme (is_victorious_false) ,
          cmd_select_ui (ui_postgame) ,
          cmd_postgame_prepare_replay
        )
        is stls_game_quit -> arrayOf (
          cmd_set_state (appst_postgame (is_victorious_false)) ,
          cmd_game_finish_replay (null) ,
          cmd_game_timer (tc_stop) ,
          cmd_postgame_set_theme (is_victorious_false) ,
          cmd_select_ui (ui_postgame) ,
          cmd_postgame_prepare_replay
        )
        else -> arrayOf ()
      }
      true -> when (stim) {
        is stls_game_pause -> when (stim.pause) {
          false -> arrayOf (
            cmd_game_timer (tc_run) ,
            cmd_set_state (appst_game (is_paused_false)))
          true -> arrayOf ()
        }
        else -> arrayOf ()
      }
    }

    is appst_postgame -> when (stim) {
      is stls_postgame_goto_menu -> arrayOf (
        cmd_set_state (appst_menu) ,
        cmd_select_ui (ui_menu) )
      is stls_postgame_play_again -> arrayOf (
        cmd_postgame_reset_map ,
        cmd_set_state (appst_game (is_paused_false)) ,
        cmd_game_timer (tc_reset) ,
        cmd_game_timer (tc_run) ,
        cmd_select_ui (ui_game) ,
        cmd_game_init_replay
      )
      is stls_postgame_download_replay -> arrayOf<command> (
        cmd_postgame_offer_replay_download )
      else -> arrayOf<command> ()
    }

    is appst_designer -> when (stim) {
      is stls_back_from_designer -> arrayOf (
        cmd_set_state (appst_menu),
        cmd_select_ui (ui_menu))
      else -> arrayOf<command> ()
    }

    else -> arrayOf ()
  }
}

data class level (
  val board : loc_map ,
  val tick_interval : game_time ,
  val max_fuel : game_fuel ,
  val starting_fuel : game_fuel ,
  val _key_fuel : HashMap<coords,game_fuel> ,
  val _door_keys : HashMap<coords,Int> ,
  val tick_cost : game_fuel ,
  val move_cost : game_fuel,
  val name : String )
{

  fun key_fuel (c : coords) : game_fuel =
    _key_fuel[c] ?: game_fuel (0)

  fun door_keys (c : coords) : Int =
    _door_keys[c] ?: 1

}

sealed class designer_mode ;
object dsm_painting : designer_mode () ;
object dsm_configuring : designer_mode () ;

enum class json_keys (val str : String) {
  player_config ("player_config") ,
  door_config ("door_config") ,
  key_config ("key_config") ,
  rows ("rows") ,
  cols ("cols") ,
  board ("board") ,
  tick_interval ("tick_interval") ,
  max_fuel ("max_fuel") ,
  starting_fuel ("starting_fuel") ,
  tick_cost ("tick_cost") ,
  move_cost ("move_cost") ,
  map_name ("name") ,
  key_fuel ("key_fuel") ,
  door_keys ("door_keys") ,
}

fun <T> Json.uget (key : json_keys) : T = this[key.str].unsafeCast<T> () ;
fun <T> Json.uget (key : String) : T = this[key].unsafeCast<T> () ;

fun coord_key (c : coords) : String = "${c.row}_${c.col}" ;
fun coord_key (row : Int, col : Int) = "${row}_${col}" ;

fun loc_to_decor_cls (l : location) : String {
  return when (l) {
    is loc_empty -> "location loc_empty"
    is loc_player -> "location loc_player"
    is loc_wall -> "location loc_wall"
    is loc_key -> "location loc_key"
    is loc_door -> when (l.opened) {
      true -> "location loc_door_open"
      false -> "location loc_door_closed"
    }
  }
}

fun loc_to_string (l : location) : String {
  return when (l) {
    is loc_empty -> "e"
    is loc_player -> "p"
    is loc_wall -> "w"
    is loc_key -> "k"
    is loc_door -> when (l.opened) {
      true -> "o"
      false -> "c"
    }
  }
}

fun string_to_loc (s : String) : location {
  return when (s) {
    "e" -> loc_empty
    "p" -> loc_player
    "w" -> loc_wall
    "k" -> loc_key
    "o" -> loc_door (true)
    "c" -> loc_door (false)
    else -> loc_wall
  }
}

fun json_to_map (rows : Int, cols : Int, raw_board : Json) : loc_map {
  val board : loc_map = mutableListOf () ;
  var ir = 0
  while (ir < rows) {
    val row = mutableListOf<location> () ;
    var ic = 0
    while (ic < cols) {
      row.add (string_to_loc (
        raw_board.uget<String> (coord_key (ir, ic))))
      ic ++ ;
    }
    board.add (row) ;
    ir ++ ;
  }
  return board ;
}

fun map_to_json (board : loc_map) : Json {
  val result = JSON.parse<Json> ("{}") ;
  for ((ir, row) in board.withIndex ()) {
    for ((ic, loc) in row.withIndex ()) {
      result.set (coord_key (ir, ic), loc_to_string (loc)) ;
    }
  }

  return result ;
}

fun json_to_coord_hash (rows : Int, cols : Int, raw : Json ,
  handler : (coords, Any?) -> Unit )
{
  var ir = 0 ;
  while (ir < rows) {
    var ic = 0 ;
    while (ic < cols) {
      handler (
        coords (ir, ic),
        raw[coord_key (ir, ic)]) ;
      ic ++ ;
    }
    ir ++ ;
  }
}

data class player_config_tile (
  val tick_interval : Double ,
  val max_fuel : Int ,
  val starting_fuel : Int ,
  val tick_cost : Int ,
  val move_cost : Int ,
  val name : String
) ;

fun json_to_player_config_tile (raw : Json) : player_config_tile {
  val tick_interval = raw.uget<Double> (json_keys.tick_interval) ;
  val max_fuel = raw.uget<Int> (json_keys.max_fuel) ;
  val starting_fuel = raw.uget<Int> (json_keys.starting_fuel) ;
  val tick_cost = raw.uget<Int> (json_keys.tick_cost) ;
  val move_cost = raw.uget<Int> (json_keys.move_cost) ;
  val name = raw.uget<String> (json_keys.map_name) ;

  return player_config_tile (
    tick_interval, max_fuel, starting_fuel, tick_cost, move_cost, name) ;
}

fun player_config_tile_to_json (obj : player_config_tile) = json (
  Pair (json_keys.tick_interval.str, obj.tick_interval) ,
  Pair (json_keys.max_fuel.str, obj.max_fuel) ,
  Pair (json_keys.starting_fuel.str, obj.starting_fuel) ,
  Pair (json_keys.tick_cost.str, obj.tick_cost) ,
  Pair (json_keys.move_cost.str, obj.move_cost) ,
  Pair (json_keys.map_name.str, obj.name)) ;

fun json_to_level (raw : Json) : level {
  val player_config = raw.uget<Json> (json_keys.player_config) ;
  var door_config = raw.uget<Json> (json_keys.door_config) ;
  var key_config = raw.uget<Json> (json_keys.key_config) ;

  val _key_fuel = hashMapOf<coords, game_fuel> () ;
  val _door_keys = hashMapOf<coords, Int> () ;

  val rows = raw.uget<Int> (json_keys.rows) ;
  val cols = raw.uget<Int> (json_keys.cols) ;
  val raw_board = raw.uget<Json> (json_keys.board) ;
  val board = json_to_map (rows, cols, raw_board) ;

  json_to_coord_hash (rows, cols, key_config, { c , v ->
    _key_fuel.put (c, game_fuel (v.unsafeCast<Int> ())) ;
  }) ;
  json_to_coord_hash (rows, cols, door_config, { c, v ->
    _door_keys.put (c, v.unsafeCast<Int> ()) ;
  }) ;

  if (loc_map_valid (board)) {
    val src = board_find (board, loc_player) ;
    val conf = player_config.uget<Json> (coord_key (src)) ;
    val pct = json_to_player_config_tile (conf) ;

    return level (board, pct.tick_interval,
      game_fuel (pct.max_fuel), game_fuel (pct.starting_fuel) ,
      _key_fuel, _door_keys,
      game_fuel (pct.tick_cost), game_fuel (pct.move_cost), pct.name) ;
  }

  return demo_level ;
}

class existing_level constructor (val raw_data : String) {

  var rows = 0 ;
  var cols = 0 ;

  var key_fuel_int = hashMapOf<coords, Int> () ;
  var door_keys_int = hashMapOf<coords, Int> () ;
  var player_config = hashMapOf<coords, player_config_tile> () ;
  var board : loc_map = mutableListOf () ;

  fun setup (r : Int, c : Int) : Unit {
    rows = r ;
    cols = c ;

    key_fuel_int = hashMapOf<coords, Int> () ;
    door_keys_int = hashMapOf<coords, Int> () ;
    player_config = hashMapOf<coords, player_config_tile> () ;
    board = mutableListOf () ;

    var ir = 0 ;
    while (ir < rows) {
      var ic = 0 ;
      var row = mutableListOf<location> () ;
      board.add (row) ;
      while (ic < cols) {
        row.add (loc_empty) ;
        ic ++ ;
      }
      ir ++ ;
    }
  }

  fun verify () : Boolean {
    try {
      val raw = JSON.parse<Json> (raw_data) ;
      rows = raw.uget<Int> (json_keys.rows) ;
      cols = raw.uget<Int> (json_keys.cols) ;
      board = json_to_map (rows, cols, raw.uget<Json> (json_keys.board)) ;
      if ( ! loc_map_valid (board)) {
        return false ;
      }

      key_fuel_int = hashMapOf<coords, Int> () ;
      json_to_coord_hash (rows, cols, raw.uget<Json> (json_keys.key_fuel), 
        { c, v -> if (! R.is_nil (v)) {
            key_fuel_int.put (c, v.unsafeCast<Int> ()) ;
          } 
        }) ;

      door_keys_int = hashMapOf<coords, Int> () ;
      json_to_coord_hash (rows, cols, raw.uget<Json> (json_keys.door_keys),
        { c, v -> if (! R.is_nil (v)) {
            door_keys_int.put (c, v.unsafeCast<Int> ()) ;
          }
        }) ;

      player_config = hashMapOf<coords, player_config_tile> () ;
      json_to_coord_hash (rows, cols, raw.uget<Json> (json_keys.player_config),
        { c, v -> if (! R.is_nil (v)) {
            player_config.put (c, json_to_player_config_tile (v.unsafeCast<Json> ())) ;
          }
        }) ;

      return true ;
    } catch (e : Throwable) {
      return false ;
    }
  }

  fun prepare_json () : Json {
    val board_json = map_to_json (board) ;
    val key_fuel_int_json = json () ;
    val door_keys_int_json = json () ;
    val player_config_json = json () ;

    for ((k,v) in key_fuel_int.entries) {
      key_fuel_int_json[coord_key (k)] = v ;
    }

    for ((k,v) in door_keys_int.entries) {
      door_keys_int_json[coord_key (k)] = v ;
    }

    for ((k,v) in player_config.entries) {
      player_config_json[coord_key (k)] = v ;
    }

    return json (
      Pair (json_keys.rows.str, rows) ,
      Pair (json_keys.cols.str, cols) ,
      Pair (json_keys.board.str, board_json) ,
      Pair (json_keys.key_fuel.str, key_fuel_int_json) ,
      Pair (json_keys.door_keys.str, door_keys_int_json) ,
      Pair (json_keys.player_config.str, player_config_json)
    ) ;
  }

  fun make_level () : level {
    val src = board_find (board, loc_player) ;
    val conf = player_config[src] ?: player_config_tile (
      1000.0, 1000, 800, 5, 20, "Tobor, The Robot"
    ) ;

    val key_fuel = hashMapOf<coords, game_fuel> () ;
    val door_keys = hashMapOf<coords, Int> () ;

    for ((k,v) in key_fuel_int.entries) {
      key_fuel.put (k, game_fuel (v)) ;
    }

    for ((k, v) in door_keys_int.entries) {
      door_keys.put (k, v) ;
    }
    
    return level (
      board,
      conf.tick_interval,
      game_fuel (conf.max_fuel) ,
      game_fuel (conf.starting_fuel) ,
      key_fuel,
      door_keys,
      game_fuel (conf.tick_cost) ,
      game_fuel (conf.move_cost) ,
      conf.name
    ) ;
  }
}

sealed class designer_stimulus ;
object ds_started : designer_stimulus () ;
object ds_new : designer_stimulus () ;
data class ds_existing (val lvl : existing_level) : designer_stimulus () ;
data class ds_existing_verified (val success : Boolean) : designer_stimulus () ;
data class ds_map_size_specified (val rows : Int, val cols : Int) : designer_stimulus () ;
object ds_quit : designer_stimulus () ;
data class ds_canvas_mouse_down (val c : coords) : designer_stimulus () ;
data class ds_canvas_mouse_in (val c : coords) : designer_stimulus () ;
object ds_canvas_mouse_up : designer_stimulus () ;
data class ds_brush_click (val l : location) : designer_stimulus () ;
data class ds_mode_picked (val m : designer_mode) : designer_stimulus () ;
object ds_done : designer_stimulus () ;
data class ds_editing_verified (val bv : Boolean) : designer_stimulus () ;
object ds_download : designer_stimulus () ;
object ds_add_to_menu : designer_stimulus () ;

sealed class designer_command ;
object dcmd_show_new_or_existing : designer_command () ;
data class dcmd_verify_dropped_file (val lvl : existing_level) : designer_command () ;
object dcmd_load_dropped_file : designer_command () ;
object dcmd_discard_dropped_file : designer_command () ;
object dcmd_show_size_picker : designer_command () ;
data class dcmd_load_new_file (val rows : Int, val cols : Int) : designer_command () ;
object dcmd_back_to_menu : designer_command () ;
data class dcmd_activate_painting (val bv : Boolean) : designer_command () ;
data class dcmd_paint_at_coord (val c : coords, val l : location) : designer_command () ;
data class dcmd_pick_brush (val l : location) : designer_command () ;
data class dcmd_enable_brush_picker (val bv : Boolean) : designer_command () ;
object dcmd_hide_config : designer_command () ;
data class dcmd_show_selection (val c : coords) : designer_command () ;
object dcmd_clear_selection : designer_command () ;
data class dcmd_showadd_key_config (val c : coords) : designer_command () ;
data class dcmd_showadd_door_config (val c : coords) : designer_command () ;
data class dcmd_showadd_map_config (val c : coords) : designer_command () ;
object dcmd_verify_editing : designer_command () ;
object dcmd_show_map_invalid : designer_command () ;
data class dcmd_show_done_screen (val bv : Boolean) : designer_command () ;
object dcmd_prepare_file : designer_command () ;
object dcmd_offer_download : designer_command () ;
object dcmd_add_to_menu : designer_command () ;

sealed class designer_state ;
object dstate_just_started : designer_state () ;
object dstate_file_picking : designer_state () ;
object dstate_size_picking : designer_state () ;
object dstate_drop_verifying : designer_state () ;
object dstate_painting : designer_state () ;
object dstate_configuring : designer_state () ;
object dstate_edit_verifying : designer_state () ;
object dstate_finalizing : designer_state () ;
object dstate_exiting : designer_state () ;

val cls_maze_table = "maze-table" ;

val demo_level : level = level (
  mutableListOf (
    mutableListOf<location> (loc_empty, loc_empty, loc_empty, loc_empty, loc_empty) ,
    mutableListOf (loc_empty, loc_empty, loc_empty, loc_wall, loc_empty) ,
    mutableListOf (loc_empty, loc_empty, loc_empty, loc_wall, loc_empty) ,
    mutableListOf (loc_player, loc_empty, loc_key, loc_wall, loc_door (false))) ,
  300.0 ,
  game_fuel (1000) ,
  game_fuel (300) ,
  hashMapOf (Pair (coords (3, 2), game_fuel (300))) ,
  hashMapOf (Pair (coords (3, 4), 1)) ,
  game_fuel (5) ,
  game_fuel (20) ,
  "Demo-01"
) ;

class UiMenu constructor (
  @JsName ("container") val parent : jquery ,
  val send : (stimulus) -> Unit
  )
{

  val root = empty_div () ;

  val cls_title = "menu-title" ;
  val cls_info = "menu-info" ;
  val cls_levels = "menu-levels" ;
  val cls_level = "menu-level" ;

  fun hide () : Unit = root.hide ()._discard () ;
  fun show () : Unit = root.show ()._discard () ;

  val info_link = ahref () ;

  val levels = empty_div () ;
  val designer = empty_div () ;

  fun setup () {
    parent.append (root) ;
    root
      .append ( empty_div ()
        .add_class (cls_title)
        .text ("Main Menu"))
      .append ( info_link
        .add_class (cls_info)
        .text ("Game Info"))
      .append ( br())
      .append ( levels
        .add_class (cls_levels))
    ;

    info_link.on_click ({ send (stls_menu_game_info) ; })

    designer.append_to (root) ;

    ahref ()
      .text ("Level Designer")
      .append_to (designer)
      .on_click ({ send (stls_menu_designer) })
  }

  fun populate_levels (ls: Array<level>) {
    levels.children ().remove () ;
    val ul = unordered_list ().append_to (levels) ;
    for ((i, l) in ls.withIndex ()) {
      val link = ahref ()
        .add_class (cls_level)
        .text (l.name)
        .on_click ({ send (stls_menu_level_selected (i)) })
      ;

      ul.append (list_item ().append (link)) ;
    }
  }
}

class UiGame constructor (
  @JsName ("container") val parent : jquery ,
  val send : (stimulus) -> Unit ,
  val current_level : () -> level?
  )
{

  val cls_game = cls_maze_table ;
  val cls_fuel = "game-fuel" ;
  val cls_keys = "game-keys" ;
  val cls_doors = "game-doors" ;

  val root = empty_div () ;
  fun hide () : Unit = root.hide ()._discard () ;
  fun show () : Unit = root.show ()._discard () ;

  val game_area = empty_div () ;
  val fuel_area = empty_div () ;
  val current_fuel = empty_div () ;
  val keys_found = empty_div () ;
  val doors_opened = empty_div () ;

  fun setup () {
    parent.append (root) ;

    root
      .append (fuel_area.add_class (cls_fuel).append (current_fuel))
      .append (game_area)
      .append (br ()).append (hr ()).append (br ())
      .append (keys_found.add_class (cls_keys))
      .append (doors_opened.add_class (cls_doors))
    ;

    empty_button ().append_to (root)
      .text ("Quit")
      .on_click ({ _ -> send (stls_game_quit) })
    ;
  }

  var board : loc_map = mutableListOf () ;
  var cells : HashMap<coords, jquery> = hashMapOf () ;
  var src : coords = coords (0, 0) ;

  fun reset () {

    val level = current_level () ;
    game_area.children ().remove () ;
    level ?. let {
      set_fuel (level.starting_fuel.remaining, level.max_fuel.remaining) ;
      val _board = level.board ;
      board = copy_loc_map (_board) ;
      src = board_find (_board, loc_player) ;
      cells = hashMapOf () ;
      val t = table ().add_class (cls_game)
        .append_to (game_area).append (table_head ()) ;
      val tb = table_body ().append_to (t) ;
      for ((row, lr) in _board.withIndex ()) {
        val r = table_row ().append_to (tb) ;
        for ((col, l) in lr.withIndex ()) {
          val d = table_data ().append_to (r) ;
          //d.text (loc_to_decor (l)) ;
          d.attr ("class", loc_to_decor_cls (l)) ;
          cells.put (coords (row, col), d) ;
        }
      }
    }
  }

  fun set_fuel (curf : Int, mf : Int) {
    val pct = curf.toDouble () * 100.0 / mf.toDouble () ;
    current_fuel.css ("width", "${pct}%") ;
    //fuel_area.text ("Fuel : $curf / $mf") ;
  }

  fun update_coords (c : coords, l : location) {
    val lr = board[c.row] ;
    lr[c.col] = l ;
    val cell = cells[c] ;
    cell ?. let {
      //cell.text (loc_to_decor (l)) ;
      cell.attr ("class", loc_to_decor_cls (l)) ;
    }
  }
}

typealias dproc_resp_type = Pair<designer_state, Array<designer_command>> ;

class UiDesigner constructor (
  @JsName ("container") val parent : jquery ,
  val send_to_menu : (stimulus) -> Unit ,
  val add_to_menu : (level) -> Unit
  )
{

  val root = empty_div () ;
  fun hide () : Unit = root.hide ()._discard () ;
  fun show () : Unit = root.show ()._discard () ;

  var painting_activated = false ;
  var current_brush : location = loc_empty ;
  var state : designer_state = dstate_just_started ;

  fun board_tile (c : coords) : location {
    return current_existing.board[c.row][c.col] ;
  }

  val file_picker = empty_div () ;
  val size_picker = empty_div () ;
  val editor = empty_div () ;
  val finalizer = empty_div () ;

  val new_file_button = empty_button () ;
  val input_size_rows = html_input ().value ("5") ;
  val input_size_cols = html_input ().value ("5") ;

  fun quit_button (l : String = "Quit") : jquery =
    empty_button ()
    .text (l)
    .on_click ({ _ -> 
      send (ds_quit) ;
    }) ;

  val brush_box = empty_div () ;
  val configure_box = empty_div () ;
  val to_config = empty_button () ;
  val to_painting = empty_button () ;
  val editing_done = empty_button () ;
  val canvas = empty_div () ;

  val level_download_a = jQuery ("<a></a>")
    .attr ("target", "_blank") ;

  // uidg setup
  fun setup () {
    parent.append (root) ;
    root
      .append (file_picker)
      .append (size_picker)
      .append (editor)
      .append (finalizer)
    ;

    empty_div ()
      .text ("click new for a new map, or drag-drop an existing map")
      .append_to (file_picker) ;

    new_file_button
      .text ("New")
      .append_to (file_picker)
      .on_click ({ _ -> send (ds_new) }) ;
  
    br ().append_to (file_picker) ;
    quit_button ().append_to (file_picker) ;

    div_label ("Specify size").append_to (size_picker) ;

    span_label ("Rows : ").append_to (size_picker) ;
    input_size_rows.append_to (size_picker) ;
    br ().append_to (size_picker) ;
    span_label ("Cols : ").append_to (size_picker) ;
    input_size_cols.append_to (size_picker) ;
    br ().append_to (size_picker) ;
    empty_button ()
      .text ("Next")
      .append_to (size_picker)
      .on_click ({ _ ->
        val rows = as_int (0, input_size_rows.value ()) ;
        val cols = as_int (0, input_size_cols.value ()) ;

        if (rows < 2 || rows > 100 || cols < 2 || cols > 100) {
          ok_dialog ("invalid size, constraint : 2 <= rows,cols <= 100") ;
        } else {
          send (ds_map_size_specified (rows, cols)) ;
        }
      })
    ;
    br ().append_to (size_picker) ;
    quit_button ().append_to (size_picker) ;

    span_label ("Brushes: ").append_to (brush_box) ;
    brush_box.append_to (editor) ;
    empty_button ()
      .text ("Empty")
      .append_to (brush_box)
      .on_click ({ _ -> send (ds_brush_click (loc_empty)) })
    empty_button ()
      .text ("Player")
      .append_to (brush_box)
      .on_click ({ _ -> send (ds_brush_click (loc_player)) })
    empty_button ()
      .text ("Wall")
      .append_to (brush_box)
      .on_click ({ _ -> send (ds_brush_click (loc_wall)) })
    empty_button ()
      .text ("Key")
      .append_to (brush_box)
      .on_click ({ _ -> send (ds_brush_click (loc_key)) })
    empty_button ()
      .text ("Door (Closed)")
      .append_to (brush_box)
      .on_click ({ _ -> send (ds_brush_click (loc_door (false))) })
    empty_button ()
      .text ("Door (Opened)")
      .append_to (brush_box)
      .on_click ({ _ -> send (ds_brush_click (loc_door (true))) })

    canvas
      .append_to (editor) ;

    configure_box.append_to (editor) ;
    quit_button ().append_to (editor) ;
    to_painting.text ("Go to Paint Mode")
      .append_to (editor)
      .on_click ({ _ -> send (ds_mode_picked (dsm_painting)) })
    ;
    to_config.text ("Go to Configuration Mode")
      .append_to (editor)
      .on_click ({ _ -> send (ds_mode_picked (dsm_configuring)) })
    ;
    editing_done.text ("Finish").append_to (editor)
      .on_click ({ _ -> send (ds_done) })
    ;

    canvas.on ("mouseup", { send (ds_canvas_mouse_up) }) ;

    empty_button ()
      .text ("Back to editing")
      .on_click ({ _ -> send (ds_mode_picked (dsm_configuring)) })
      .append_to (finalizer) ;

    level_download_a
      .text ("Download map")
      .append_to (finalizer) ;

    empty_button ()
      .text ("Add map to menu")
      .on_click ({ _ -> send (ds_add_to_menu) })
      .append_to (finalizer) ;

    quit_button ()
      .text ("Back to menu")
      .append_to (finalizer) ;
  }

  fun reset () {
    painting_activated = false ;
    current_brush = loc_empty ;
    state = dstate_just_started ;
  }

  fun process (st : designer_state , sim : designer_stimulus) :
    Pair<designer_state, Array<designer_command>>
  {

    val nothing = Pair (st, arrayOf<designer_command> ()) ;

    return when (sim) {
      // dproc_started
      is ds_started -> when (st) {
        is dstate_just_started -> Pair (dstate_file_picking, 
          arrayOf<designer_command> (dcmd_show_new_or_existing))
        else -> nothing
      }

      // dproc_new_option
      is ds_new -> when (st) {
        is dstate_file_picking -> Pair (dstate_size_picking,
          arrayOf<designer_command> (dcmd_show_size_picker))
        else -> nothing
      }

      // dproc_new_painting
      is ds_map_size_specified -> when (st) {
        is dstate_size_picking -> Pair (dstate_painting, arrayOf (
          dcmd_load_new_file (sim.rows, sim.cols) ,
          dcmd_pick_brush (loc_empty) ,
            dcmd_enable_brush_picker (true) ,
          dcmd_hide_config ))
        else -> nothing
      }

      // dproc_existing_dropped
      is ds_existing -> when (st) {
        is dstate_file_picking -> Pair (dstate_drop_verifying,
          arrayOf<designer_command> (dcmd_verify_dropped_file (sim.lvl)))
        else -> nothing
      }

      is ds_existing_verified -> when (sim.success) {
        // dproc_existing_verified
        true -> when (st) {
          is dstate_drop_verifying -> Pair (dstate_painting, arrayOf (
            dcmd_load_dropped_file ,
            dcmd_pick_brush (loc_empty) ,
            dcmd_enable_brush_picker (true) ,
            dcmd_hide_config ))
          else -> nothing
        }
        // dproc_existing_failed_verification
        false -> when (st) {
          is dstate_drop_verifying -> dproc_resp_type (dstate_file_picking, arrayOf (
            dcmd_show_map_invalid ,
            dcmd_discard_dropped_file ))
          else -> nothing
        }
      }

      is ds_canvas_mouse_down -> when (st) {
        // dproc_mouse_down_canvas
        is dstate_painting -> Pair (dstate_painting, arrayOf (
          dcmd_activate_painting (true) ,
          dcmd_paint_at_coord (sim.c, current_brush) ))
        is dstate_configuring -> when (board_tile (sim.c)) {
          // dproc_configuring_player
          is loc_player -> Pair (dstate_configuring, arrayOf (
            dcmd_hide_config ,
            dcmd_showadd_map_config (sim.c) ,
            dcmd_clear_selection ,
            dcmd_show_selection (sim.c) ))
          // dproc_configuring_door
          is loc_door -> Pair (dstate_configuring, arrayOf (
            dcmd_hide_config ,
            dcmd_showadd_door_config (sim.c) ,
            dcmd_clear_selection ,
            dcmd_show_selection (sim.c) ))
          // dproc_configuring_key
          is loc_key -> Pair (dstate_configuring, arrayOf (
            dcmd_hide_config ,
            dcmd_showadd_key_config (sim.c) ,
            dcmd_clear_selection ,
            dcmd_show_selection (sim.c) ))
          else -> nothing
        }
        else -> nothing
      }

      // dproc_mouse_in_canvas
      is ds_canvas_mouse_in -> when (st) {
        is dstate_painting -> when (painting_activated) {
          true -> Pair ( dstate_painting ,
            arrayOf<designer_command> (dcmd_paint_at_coord (sim.c, current_brush)))
          false -> nothing
        }
        else -> nothing
      }

      // dproc_mouse_up_canvas
      is ds_canvas_mouse_up -> when (st) {
        is dstate_painting -> when (painting_activated) {
          true -> Pair ( dstate_painting ,
            arrayOf<designer_command> (dcmd_activate_painting (false)))
          false -> nothing
        }
        else -> nothing
      }

      // dproc_brush_selected
      is ds_brush_click -> when (st) {
        is dstate_painting -> Pair (dstate_painting ,
          arrayOf<designer_command> (dcmd_pick_brush (sim.l)))
        else -> nothing
      }

      is ds_mode_picked -> when (sim.m) {
        is dsm_configuring -> when (st) {
          // dproc_mode_to_configuring
          is dstate_painting -> Pair (dstate_configuring , arrayOf (
            dcmd_enable_brush_picker (false) ,
            dcmd_hide_config ,
            dcmd_clear_selection ))
          // dproc_back_to_editing
          is dstate_finalizing -> Pair (dstate_configuring, arrayOf (
            dcmd_show_done_screen (false) ,
            dcmd_enable_brush_picker (false) ,
            dcmd_hide_config ,
            dcmd_clear_selection ))
          else -> nothing
        }
        // dproc_mode_to_painting
        is dsm_painting -> when (st) {
          is dstate_configuring -> Pair (dstate_painting , arrayOf (
            dcmd_hide_config ,
            dcmd_enable_brush_picker (true) ,
            dcmd_clear_selection ))
          else -> nothing
        }
      }

      is ds_done -> when (st) {
        // dproc_verifying_editing
        is dstate_configuring -> Pair (dstate_edit_verifying ,
          arrayOf<designer_command> ( dcmd_verify_editing ))
        // dproc_verifying_editing_paint
        is dstate_painting -> Pair (dstate_edit_verifying ,
          arrayOf<designer_command> ( dcmd_verify_editing ))
        else -> nothing
      }

      is ds_editing_verified -> when (st) {
        is dstate_edit_verifying -> when (sim.bv) {
          // dproc_verifying_failed
          false -> Pair (dstate_configuring , arrayOf ( 
            dcmd_hide_config ,
            dcmd_enable_brush_picker (false) ,
            dcmd_clear_selection ,
            dcmd_show_map_invalid ))
          // dproc_verifying_success
          true -> dproc_resp_type (dstate_finalizing , arrayOf (
            dcmd_prepare_file ,
            dcmd_show_done_screen (true)))
          }
        else -> nothing
      }

      // dproc_downloading
      is ds_download -> when (st) {
        is dstate_finalizing -> Pair (dstate_finalizing ,
          arrayOf<designer_command> ( dcmd_offer_download ))
        else -> nothing
      }

      // dproc_adding_to_menu
      is ds_add_to_menu -> when (st) {
        is dstate_finalizing -> Pair (dstate_finalizing ,
          arrayOf<designer_command> ( dcmd_add_to_menu ))
        else -> nothing
      }

      // dproc_back_to_menu
      is ds_quit -> Pair (dstate_exiting,
        arrayOf<designer_command> ( dcmd_back_to_menu ))
    }
  }

  fun send (stim : designer_stimulus) : Unit {
    val curst = state ;
    sched (0, {
      val (nstate, cmds) = process (curst, stim) ;
      state = nstate ;
      for (cmd in cmds) {
        run_command (cmd) ;
      }
    }) ;
  }

  fun file_dropped (contents : String) : Unit {
    send (ds_existing (existing_level (contents))) ;
  }

  fun show_file_picker () : Unit {
    root.children ().hide () ;
    file_picker.show () ;
  }

  fun show_size_picker () : Unit {
    root.children ().hide () ;
    size_picker.show () ;
  }

  fun show_editor () : Unit {
    root.children ().hide () ;
    editor.show () ;
  }

  var canvas_body = table_body () ;

  fun setup_editor () : Unit {
    canvas.children ().remove () ;
    val table = table ()
      .add_class (cls_maze_table)
      .add_class ("design-phase")
    ;
    table.append_to (canvas) ;
    table.append (table_head ()) ;
    canvas_body = table_body () ;
    table.append (canvas_body) ;

    for ((ir,row) in current_existing.board.withIndex ()) {
      val trow = table_row () ;
      canvas_body.append (trow) ;
      for ((ic,loc) in row.withIndex ()) {
        val td = table_data () ;
        trow.append (td) ;
        //td.text (loc_to_decor (loc)) ;
        td.attr ("class", loc_to_decor_cls (loc)) ;
        td
          .on ("mousedown", 
            { _ -> send (ds_canvas_mouse_down (coords (ir, ic))) }) 
          .on ("mouseover",
            { _ -> send (ds_canvas_mouse_in (coords (ir, ic))) })
        ;
      }
    }
  }

  fun show_finalizer () : Unit {
    root.children ().hide () ;
    finalizer.show () ;
  }

  var current_existing = existing_level ("") ;

  fun run () {
    reset () ;
    send (ds_started) ;
  }

  // uidg run_command
  fun run_command (cmd : designer_command) {
    when (cmd) {
      is dcmd_show_new_or_existing -> show_file_picker ()
      is dcmd_verify_dropped_file -> when (cmd.lvl.verify ()) {
        true -> {
          current_existing = cmd.lvl ;
          send (ds_existing_verified (true))
        }
        false -> {
          send (ds_existing_verified (false)) ;
        }
      }
      is dcmd_load_dropped_file -> {
        setup_editor () ;
        show_editor () ;
      }
      is dcmd_discard_dropped_file -> { }
      is dcmd_show_size_picker -> show_size_picker () 
      is dcmd_load_new_file -> { 
        current_existing.setup (cmd.rows, cmd.cols) ;
        setup_editor () ;
        show_editor () ;
      }
      is dcmd_back_to_menu -> send_to_menu (stls_back_from_designer)
      is dcmd_activate_painting -> { painting_activated = cmd.bv }
      is dcmd_paint_at_coord -> {
        current_existing.board[cmd.c.row][cmd.c.col] = cmd.l ;
        canvas_body.children ().eq (cmd.c.row).children ().eq (cmd.c.col)
          //.text (loc_to_decor (cmd.l)) ;
          .attr ("class", loc_to_decor_cls (cmd.l)) ;
      }
      is dcmd_pick_brush -> { current_brush = cmd.l }
      is dcmd_enable_brush_picker -> when (cmd.bv) {
        true -> { brush_box.show () ; to_painting.hide () ; to_config.show () ; }
        false -> { brush_box.hide () ; to_painting.show () ; to_config.hide () ; }
      }
      is dcmd_hide_config -> {
        save_config () ;
        configure_box.hide () ;
      }
      is dcmd_show_selection -> canvas_body
        .children ().eq (cmd.c.row).children ().eq (cmd.c.col)
        .text ("X") ;
      is dcmd_clear_selection -> canvas_body
        .find ("td").text ("")
      is dcmd_showadd_key_config -> configure_key_at (cmd.c)
      is dcmd_showadd_door_config -> configure_door_at (cmd.c)
      is dcmd_showadd_map_config -> configure_player_at (cmd.c)
      is dcmd_verify_editing -> {
        save_config () ;
        send ( ds_editing_verified (
          loc_map_valid (current_existing.board))) ;
      }
      is dcmd_show_map_invalid -> ok_dialog ("map is invalid")
      is dcmd_show_done_screen -> when (cmd.bv) {
        true -> { save_config () ; show_finalizer () ; }
        false -> show_editor ()
      }
      is dcmd_prepare_file -> level_download_a.attr ("href", json_download_url (
          current_existing.prepare_json ())) ;
      is dcmd_offer_download -> { }
      is dcmd_add_to_menu -> add_to_menu (current_existing.make_level ())
    }
  }

  var config_writer : () -> Unit = { }

  fun save_config () : Unit {
    config_writer () ;
    config_writer = { }
  }

  fun configure_key_at (c : coords) : Unit {
    save_config () ;
    configure_box.show () ;
    configure_box.children ().remove () ;
    val fuel_input = html_input ().value ("0") ;

    span_label ("Fuel : ").append_to (configure_box) ;
    fuel_input.append_to (configure_box) ;

    val kf = current_existing.key_fuel_int[c] ;
    kf ?. let {
      fuel_input.value (kf.toString ()) ;
    }

    config_writer = {
      current_existing.key_fuel_int[c] =
        as_int (0, fuel_input.value ()) ;
    }
  }

  fun configure_door_at (c : coords) : Unit {
    save_config () ;
    configure_box.show () ;
    configure_box.children ().remove () ;
    val keys_input = html_input () ;
    val opened_input = html_input ("checkbox") ;

    span_label ("Keys : ").append_to (configure_box) ;
    keys_input.append_to (configure_box).value ("1") ;
    br ().append_to (configure_box) ;

    span_label ("Opened : ").append_to (configure_box) ;
    opened_input.append_to (configure_box) ;
    val door = current_existing.board[c.row][c.col] ;
    when (door) {
      is loc_door -> opened_input.checked (door.opened)
      else -> { }
    }

    opened_input.on ("change", { _ ->
      canvas_body.children ().eq (c.row).children ().eq (c.col)
        .attr ("class", loc_to_decor_cls (loc_door (opened_input.checked ()))) ;
    }) ;

    val dk = current_existing.door_keys_int[c] ;
    dk ?. let {
      keys_input.value (dk.toString ()) ;
    }

    config_writer = {
      current_existing.door_keys_int[c] =
        as_int (1, keys_input.value ()) ;
      val _door = current_existing.board[c.row][c.col] ;
      when (_door) {
        is loc_door -> {
          current_existing.board[c.row][c.col] = loc_door (opened_input.checked ()) ;
          canvas_body.children ().eq (c.row).children ().eq (c.col)
            .attr ("class", loc_to_decor_cls (loc_door (opened_input.checked ()))) ;
        }
        else -> { }
      }
    }
  } // configure_door

  fun configure_player_at (c : coords) : Unit {
    save_config () ;
    configure_box.show () ;
    configure_box.children ().remove () ;
    val tick_interval_input = html_input () ;
    val max_fuel_input = html_input () ;
    val starting_fuel_input = html_input () ;
    val tick_cost_input = html_input () ;
    val move_cost_input = html_input () ;
    val name_input = html_input () ;

    fun add_with_label (l : String, w : jquery, v : String) {
      span_label (l).append_to (configure_box) ;
      w.append_to (configure_box).value (v) ;
      br ().append_to (configure_box) ;
    }

    add_with_label ("Tick Interval (millis) : ", tick_interval_input, "1000") ;
    add_with_label ("Max Fuel : ", max_fuel_input, "1000") ;
    add_with_label ("Starting Fuel : ", starting_fuel_input, "750") ;
    add_with_label ("Fuel cost per tick : ", tick_cost_input, "5") ;
    add_with_label ("Fuel per move : ", move_cost_input, "10") ;
    add_with_label ("Name : ", name_input, "Tobor, The Robot") ;

    val svals = current_existing.player_config[c] ;
    svals ?. let {
      tick_interval_input.value (svals.tick_interval.toString ()) ;
      max_fuel_input.value (svals.max_fuel.toString ()) ;
      starting_fuel_input.value (svals.starting_fuel.toString ()) ;
      tick_cost_input.value (svals.tick_cost.toString ()) ;
      move_cost_input.value (svals.move_cost.toString ()) ;
      name_input.value (svals.name.toString ()) ;
    }

    config_writer = {
      current_existing.player_config[c] = player_config_tile (
        tick_interval = as_double (1000.0, tick_interval_input.value ()) ,
        max_fuel = as_int (1000, max_fuel_input.value ()) ,
        starting_fuel = as_int (750, starting_fuel_input.value ()) ,
        tick_cost = as_int (5, tick_cost_input.value ()) ,
        move_cost = as_int (20, move_cost_input.value ()) ,
        name = name_input.value ()
      ) ;
    }
  }
}

class Executor {

  var m_app_state : app_state = appst_launched ;

  fun run () : Unit {

    jQuery (window).on ("dragover", { evt ->
      evt.prevent_default () ;
    }) ;

    jQuery (window).on ("drop", { evt ->
      evt.prevent_default () ;

      val files = evt.original_event.data_transfer.files ;

      if (files.length == 1) {
        file_dropped (files.item (0)) ;
      }
    }) ;

    send (stls_launched) ;
  }

  fun send (stim : stimulus) : Unit {
    sched (0, {
      val cmds = process (m_app_state, stim) ;
      for (cmd in cmds) {
        run_command (cmd) ;
      }
    }) ;
  }

  var builtin_levels = arrayOf<level> () ;
  var selected_level : level = demo_level ;
  var current_fuel = game_fuel (0) ;
  var current_keys = 0 ;

  fun current_tick_cost () : Int = selected_level.tick_cost.remaining ;
  fun current_move_cost () : Int = selected_level.move_cost.remaining ;
  fun current_max_fuel () : Int  = selected_level.max_fuel.remaining ;

  var m_process_move : process_move? = null ;

  // execcmd
  fun run_command (cmd : command) : Unit {
    when (cmd) {

      is cmd_setup_ui -> setup_ui ()
      is cmd_set_state -> { m_app_state = cmd.state }
      is cmd_select_ui -> select_ui (cmd.ui)

      is cmd_menu_fetch_builtin_levels -> if (loc_map_valid (demo_level.board)) {
        builtin_levels = arrayOf (demo_level) ;
        send (stls_menu_levels_fetched) ;
      }
      is cmd_menu_populate -> m_ui_menu.populate_levels (builtin_levels)
      is cmd_menu_select_level -> { selected_level = builtin_levels[cmd.li] ; }

      is cmd_game_timer -> m_timer_control (cmd.tc)
      is cmd_game_pause -> { }
      is cmd_game_fuel_tick -> {
        current_fuel.remaining -= current_tick_cost () ;
        m_ui_game.set_fuel (current_fuel.remaining, current_max_fuel ()) ;
        if (current_fuel.remaining <= 0) {
          send (stls_game_fuel_empty) ;
        }
      }
      is cmd_game_process_move -> {
        val pm = m_process_move ;
        pm ?. let {
          val mcmds = pm (cmd.m) ;
          for (mcmd in mcmds) {
            run_move_command (mcmd) ;
          }
        }
      }

      is cmd_postgame_reset_map -> m_ui_game.reset ()
      is cmd_postgame_set_theme -> setpgm_msg (cmd.is_vict)
      is cmd_postgame_prepare_replay -> { }
      is cmd_postgame_offer_replay_download -> { }

      is cmd_transfer_to_designer -> m_ui_designer.run ()
      else -> { }
    }
  }

  fun iterboard (fn : (coords, location, (location) -> Unit) -> Unit) {
    var board = m_ui_game.board ;
    val rows = board.size ;
    val cols = board[0].size ;
    var ir = 0 ;
    while (ir < rows) {
      val row = board[ir] ;
      var ic = 0 ;
      while (ic < cols) {
        val l = row[ic] ;
        fn (coords (ir, ic), l, { xl -> row[ic] = xl }) ;
        ic ++ ;
      }
      ir ++ ;
    }
  }

  // execmvcmd
  fun run_move_command (cmd : move_command) : Unit {
    when (cmd) {
      is mvcmd_update_coords -> m_ui_game.update_coords (cmd.c, cmd.l)
      is mvcmd_key_update_doors -> {
        current_keys += 1 ;
        iterboard ({ c, l, setter ->
          when (l) {
            is loc_door -> when (l.opened) {
              false -> when (current_keys >= selected_level.door_keys (c)) {
                true -> {
                  setter (loc_door (true)) ;
                  m_ui_game.update_coords (c, loc_door (true)) ;
                }
                false -> { }
              }
              true -> { }
            }
            else -> { }
          }
        }) ;
      }
      is mvcmd_trigger_victory -> send (stls_game_victory)
      is mvcmd_expend_fuel -> { 
        current_fuel.remaining -= current_move_cost () ;
        if (current_fuel.remaining > selected_level.max_fuel.remaining) {
          current_fuel.remaining = selected_level.max_fuel.remaining ;
        }
        if (current_fuel.remaining <= 0) {
          send (stls_game_fuel_empty) ;
        }
        m_ui_game.set_fuel (current_fuel.remaining, current_max_fuel ()) ;
      }
      is mvcmd_update_player_coords -> {
        m_ui_game.src.row = cmd.c.row ;
        m_ui_game.src.col = cmd.c.col ;
      }
      is mvcmd_append_to_replay -> { }
      is mvcmd_add_fuel -> {
        val topup = selected_level.key_fuel (cmd.c).remaining ;
        current_fuel.remaining += topup ;
        if (current_fuel.remaining > selected_level.max_fuel.remaining) {
          current_fuel.remaining = selected_level.max_fuel.remaining ;
        }
        if (current_fuel.remaining <= 0) {
          send (stls_game_fuel_empty) ;
        }
        m_ui_game.set_fuel (current_fuel.remaining, current_max_fuel ()) ;
      }
    }
  }

  fun add_to_menu (l : level) : Unit {
    builtin_levels = builtin_levels + l ;
    m_ui_menu.populate_levels (builtin_levels) ;
  }

  val cls_main = ".main" ;
  val m_main : jquery
    get () = jQuery (cls_main) ;

  val m_ui_game = UiGame (m_main, { s -> send (s) }, { selected_level }) ;
  val m_ui_postgame = empty_div () ;
  val m_ui_menu = UiMenu (m_main, { s -> send (s) })
  val m_ui_designer = UiDesigner (m_main, { s -> send (s) }, { l -> add_to_menu (l) })
  val m_ui_replay = empty_div () ;

  val pgm_message = empty_div () ;

  fun setpgm_msg (did_we_win : Boolean) : Unit = when (did_we_win) {
    true -> pgm_message.text ("Victory !")._discard ()
    false -> pgm_message.text ("Game Over :(")._discard ()
  }

  fun setup_ui () : Unit {
    m_ui_menu.setup () ;
    m_ui_game.setup () ;
    m_ui_designer.setup () ;
    m_main.append (m_ui_postgame) ;
    m_main.children ().hide () ;
    jQuery (document).on_keydown ({ evt -> key_released (evt.which) }) ;

    pgm_message.append_to (m_ui_postgame) ;
    empty_button ()
      .text ("Play Again")
      .append_to (m_ui_postgame)
      .on_click ({ _ -> send (stls_postgame_play_again) })
    ;

    empty_button ()
      .text ("Back to Menu")
      .append_to (m_ui_postgame)
      .on_click ({ _ -> send (stls_postgame_goto_menu) })
    ;
  }

  fun key_released (code : Int) {
    when (code) {
      37 -> send (stls_game_moved (mv_left)) // left
      39 -> send (stls_game_moved (mv_right)) // right
      38 -> send (stls_game_moved (mv_up)) // up
      40 -> send (stls_game_moved (mv_down)) // down
      else -> { }
    }
  }

  fun select_ui (ui : major_ui) : Unit {
    m_main.children ().hide () ;
    m_process_move = null ;
    when (ui) {
      is ui_game -> prepare_and_show_game_ui () ;
      is ui_postgame -> m_ui_postgame.show () ;
      is ui_menu -> m_ui_menu.show () ;
      is ui_designer -> m_ui_designer.show () ;
      is ui_replay -> m_ui_replay.show () ;
    }
  }

  fun prepare_and_show_game_ui () : Unit {
    current_fuel.remaining = selected_level.starting_fuel.remaining ;
    current_keys = 0 ;
    m_ui_game.reset () ;
    val board = m_ui_game.board ;
    val mrow = board.size
    val col = board.getOrNull (0) ;
    col ?. let {
      m_process_move = process_move (
        mrow - 1, col.size - 1, board, m_ui_game.src) ;
    }
    m_ui_game.show () ;
  }

  fun current_tick_interval () : game_time
    = selected_level.tick_interval ;

  var t_last_time : game_time = 0.0 ;
  fun tick () {
    t_last_time = current_time () ;
    send (stls_game_tick) ;
  }

  var timer_handle : Int? = null ;

  fun t_interval_start (fti : game_time) {
    sched (fti, {
      tick () ;
      timer_handle = window.setInterval ({ tick () ; }, 
        current_tick_interval ().toInt () ) ;
    }) ;
  }

  fun t_interval_stop () {
    val th = timer_handle ;
    th ?. let { window.clearInterval (th) ; }
    timer_handle = null ;
  }

  var t_rem_time : game_time = 0.0 ;

  fun m_timer_control (tc : timer_control) {
    when (tc) {
      is tc_reset -> {
        t_rem_time = current_tick_interval () ;
        t_interval_stop () ;
      }
      is tc_run -> {
        t_interval_start (t_rem_time) ;
      }
      is tc_stop -> {
        t_rem_time = current_tick_interval () ;
        t_interval_stop () ;
      }
      is tc_pause -> {
        t_rem_time = current_time () - t_last_time ;
        t_interval_stop () ;
      }
    }
  }

  fun file_dropped (f : file_interface) : Unit {
    if (f.is_json () && f.size < 1000000) {
      val reader = file_reader () ;
      reader.read_text_file (f, { contents ->
        m_ui_designer.file_dropped (contents)
      }) ;
    }
  }
}

var executor : Executor? = null ;

fun main (s : Array<String>) {
  jQuery (window).on_load ( {
    executor = Executor () ;
    executor?.run () ;
  }) ;
}

