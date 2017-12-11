package maze ;

import kotlin.js.* ;
import kotlin.browser.* ;
import org.w3c.dom.Window ;
import org.w3c.dom.Document ;
import kotlin.collections.MutableSet ;
import kotlin.collections.MutableList ;
import kotlin.text.StringBuilder ;

// ------------- Module Helpers. -------------------

fun Any?._discard () = Unit ;

fun current_time () : Double { return Date ().getTime () ; }
fun sched (ms : Double, fn : () -> Unit) = window.setTimeout (fn, ms.toInt ()) ;
fun sched (ms : Int, fn : () -> Unit) = window.setTimeout (fn, ms) ;

external interface jquery {

  interface event {
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

  fun children (x : String = definedExternally) : jquery ;
  @JsName ("click")
  fun on_click (fn : (evt: event) -> Unit) : jquery ;

  fun hide () : jquery ;

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
}

external fun jQuery (x : String = definedExternally) : jquery ;
external fun jQuery (x : Window) : jquery ;
external fun jQuery (x : Document) : jquery ;

fun jquery.on_load (fn : (jquery.event) -> Unit) : jquery 
  = this.on ("load", fn) ;

fun empty_div () : jquery =
  jQuery ("<div></div>") ;

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
fun table () : jquery = jQuery ("<table></table>") ;
fun table_head () : jquery = jQuery ("<thead></thead>") ;
fun table_body () : jquery = jQuery ("<tbody></tbody>") ;
fun table_row () : jquery = jQuery ("<tr></tr>") ;
fun table_data () : jquery = jQuery ("<td></td>") ;

// ------------------ End Helpers. ------------------

// ------------------ Module Spec. ------------------

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

// ------------------ End Spec. ------------------

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

class UiGame constructor (
  @JsName ("container") val parent : jquery ,
  val send : (stimulus) -> Unit ,
  val current_level : () -> level?
  )
{

  val cls_game = "game-main" ;
  val cls_fuel = "game-fuel" ;
  val cls_keys = "game-keys" ;
  val cls_doors = "game-doors" ;

  val root = empty_div () ;
  fun hide () : Unit = root.hide ()._discard () ;
  fun show () : Unit = root.show ()._discard () ;

  val game_area = empty_div () ;
  val fuel_area = empty_div () ;
  val keys_found = empty_div () ;
  val doors_opened = empty_div () ;

  fun setup () {
    parent.append (root) ;

    root
      .append (game_area.add_class (cls_game))
      .append (br ()).append (hr ()).append (br ())
      .append (fuel_area.add_class (cls_fuel))
      .append (keys_found.add_class (cls_keys))
      .append (doors_opened.add_class (cls_doors))
    ;
  }

  var board : loc_map? = null ;
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
      val t = table ().append_to (game_area).append (table_head ()) ;
      val tb = table_body ().append_to (t) ;
      for ((row, lr) in _board.withIndex ()) {
        val r = table_row ().append_to (tb) ;
        for ((col, l) in lr.withIndex ()) {
          val d = table_data ().append_to (r) ;
          decorate_cell (d, l) ;
          cells.put (coords (row, col), d) ;
        }
      }
    }
  }

  fun set_fuel (curf : Int, mf : Int) {
    val sb = StringBuilder () ;
    sb.append ("Fuel : ")
    sb.append (curf) ;
    sb.append (" / ") ;
    sb.append (mf) ;
    fuel_area.text (sb.toString ()) ;
  }

  fun decorate_cell (cell : jquery, l : location) {
    when (l) {
      is loc_empty -> cell.text (".")
      is loc_player -> cell.text ("P")
      is loc_wall -> cell.text ("+")
      is loc_key -> cell.text ("$")
      is loc_door -> when (l.opened) {
        false -> cell.text ("X")
        true -> cell.text ("!")
      }
    }
  }

  fun update_coords (c : coords, l : location) {
    val _board = board ;
    _board ?. let {
      val lr = _board[c.row] ;
      lr[c.col] = l ;
      val cell = cells[c] ;
      cell ?. let {
        decorate_cell (cell, l) ;
      }
    }
  }
}

class Executor {

  var m_app_state : app_state = appst_launched ;

  fun run () : Unit {
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
  var selected_level : level? = null ;
  var current_fuel = game_fuel (0) ;

  fun current_tick_cost () : Int {
    val tk = selected_level ?. tick_cost ;
    return tk ?. remaining ?: 0 ;
  }

  fun current_move_cost () : Int {
    val tk = selected_level ?. move_cost ;
    return tk ?. remaining ?: 1 ;
  }

  fun current_max_fuel () : Int {
    val tk = selected_level ?. max_fuel ;
    return tk ?. remaining ?: 10 ;
  }

  var m_process_move : process_move? = null ;

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
      else -> { }
    }
  }

  fun run_move_command (cmd : move_command) : Unit {
    when (cmd) {
      is mvcmd_update_coords -> m_ui_game.update_coords (cmd.c, cmd.l)
      is mvcmd_key_update_doors -> { }
      is mvcmd_trigger_victory -> { }
      is mvcmd_expend_fuel -> { 
        current_fuel.remaining -= current_move_cost () ;
        m_ui_game.set_fuel (current_fuel.remaining, current_max_fuel ()) ;
        if (current_fuel.remaining <= 0) {
          send (stls_game_fuel_empty) ;
        }
      }
      is mvcmd_update_player_coords -> {
        m_ui_game.src.row = cmd.c.row ;
        m_ui_game.src.col = cmd.c.col ;
      }
      is mvcmd_append_to_replay -> { }
      is mvcmd_add_fuel -> { cmd.c }
    }
  }

  val cls_main = ".main" ;
  val m_main : jquery
    get () = jQuery (cls_main) ;

  val m_ui_game = UiGame (m_main, { s -> send (s) }, { selected_level }) ;
  val m_ui_postgame = empty_div () ;
  val m_ui_menu = UiMenu (m_main, { s -> send (s) })
  val m_ui_designer = empty_div () ;
  val m_ui_replay = empty_div () ;

  fun setup_ui () : Unit {
    m_ui_menu.setup () ;
    m_ui_game.setup () ;
    m_main.children ().hide () ;
    jQuery (document).on_keydown ({ evt -> key_released (evt.which) }) ;
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
    current_fuel.remaining = selected_level?.starting_fuel?.remaining ?: 0 ;
    m_ui_game.reset () ;
    val board = m_ui_game.board ;
    board ?. let {
      val mrow = board.size
      val col = board.getOrNull (0) ;
      col ?. let {
        m_process_move = process_move (
          mrow - 1, col.size - 1, board, m_ui_game.src) ;
      }
    }
    m_ui_game.show () ;
  }

  fun current_tick_interval () : game_time
    = selected_level ?. tick_interval ?: 1000.0 ;

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
}

var executor : Executor? = null ;

fun main (s : Array<String>) {
  jQuery (window).on_load ( {
    executor = Executor () ;
    executor?.run () ;
  }) ;
}

