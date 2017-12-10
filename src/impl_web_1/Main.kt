package maze ;

import kotlin.js.* ;
import kotlin.browser.* ;
import kotlin.collections.MutableSet ;
import kotlin.collections.MutableList ;

fun current_time () : Double { return Date ().getTime () ; }

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
      is mv_up -> if (src.row == 0) null else src.copy (src.row - 1)
      is mv_down -> if (src.row == mrow) null else src.copy (src.row + 1)
      is mv_left -> if (src.col == 0) null else src.copy (src.col - 1)
      is mv_right -> if (src.col == mcol) null else src.copy (src.col + 1)
    }
  }

  fun map_location (c : coords) : location = 
    board[c.row][c.col] ;

  fun invoke (mv : movement) : Array<move_command> {
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
        cmd_set_state (appst_menu) ,
        cmd_menu_fetch_builtin_levels ,
        cmd_menu_populate )
      else -> arrayOf ()
    }

    is appst_menu -> when (stim) {
      is stls_menu_level_selected -> arrayOf (
        cmd_menu_select_level (stim.li) ,
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
  val move_cost : game_fuel )
{

  fun key_fuel (c : coords) : game_fuel =
    _key_fuel[c] ?: game_fuel (0)

  fun door_keys (c : coords) : Int =
    _door_keys[c] ?: 1

}

fun main (s : Array<String>) {
}

