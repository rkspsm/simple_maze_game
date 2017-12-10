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

fun clone_loc_map (l : loc_map) : loc_map {
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

sealed class replay_control ;
data class rep_init (val gt : game_time) : replay_control () ;
data class rep_append (
  val st : start_time,
  val gt : game_time,
  val fuel : game_fuel,
  val lm : loc_map) : replay_control () ;
data class rep_finish (
  val st : start_time,
  val gt : game_time,
  val is_vict : is_victorious) : replay_control () ;
data class rep_abort (val st : start_time, val gt : game_time) : replay_control () ;

sealed class replay_command ;
data class rcmd_set_start_time (val gt : game_time) : replay_command () ;
data class rcmd_add_map
  (val gt : game_time, val fuel : game_fuel, val lm : loc_map) : replay_command () ;
data class rcmd_set_abort (val gt : game_time) : replay_command () ;
data class rcmd_set_victory (val gt : game_time) : replay_command () ;
data class rcmd_set_loss (val gt : game_time) : replay_command () ;

fun replay_process (rc : replay_control) : Array<replay_command> {
  return when (rc) {
    is rep_init -> arrayOf (rcmd_set_start_time (rc.gt))
    is rep_append -> arrayOf (rcmd_add_map ((rc.gt - rc.st), rc.fuel, rc.lm))
    is rep_finish -> when (rc.is_vict) {
      false -> arrayOf<replay_command> (rcmd_set_loss (rc.gt - rc.st))
      true -> arrayOf<replay_command> (rcmd_set_loss (rc.gt - rc.st)) }
    is rep_abort -> arrayOf (rcmd_set_abort (rc.gt - rc.st))
  }
}

sealed class move_command ;
data class mvcmd_update_coords (val c : coords, val l : location) : move_command () ;
object mvcmd_key_update_doors : move_command () ;
object mvcmd_trigger_victory : move_command () ;
object mvcmd_expend_fuel : move_command () ;
data class mvcmd_update_player_coords (val c : coords) : move_command () ;
object mvcmd_append_to_replay : move_command () ;
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
          mvcmd_append_to_replay )
        is loc_key -> arrayOf (
          mvcmd_update_coords (src, loc_empty),
          mvcmd_update_coords (_dest, loc_player),
          mvcmd_update_player_coords (_dest),
          mvcmd_add_fuel (_dest),
          mvcmd_append_to_replay )
        is loc_door -> when (loc.opened) {
          false -> arrayOf ()
          true -> arrayOf (
            mvcmd_update_coords (src, loc_empty),
            mvcmd_update_coords (_dest, loc_player),
            mvcmd_update_player_coords (_dest),
            mvcmd_append_to_replay,
            mvcmd_trigger_victory )
        }
        else -> arrayOf ()
      }
    }

    return arrayOf () ;
  }

}

class replay_context constructor (
  val lm : loc_map,
  val fuel : game_fuel,
  val st : start_time)
{
  val gt : game_time
    get () = current_time () ;

  fun relproc_move_replay (cmd : move_command) : Array<replay_control> {
    return when (cmd) {
      is mvcmd_append_to_replay -> arrayOf (
        rep_append (st, gt, fuel.copy (), clone_loc_map (lm)))
      else -> arrayOf ()
    }
  }
}

fun main (s : Array<String>) {
}

