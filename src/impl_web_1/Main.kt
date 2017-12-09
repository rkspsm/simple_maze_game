package maze ;

sealed class location ;
data class loc_empty (val ig : Unit = Unit) : location () ;
data class loc_player (val ig : Unit = Unit) : location () ;
data class loc_wall (val ig : Unit = Unit) : location () ;
data class loc_key (val ig : Unit = Unit) : location () ;
data class loc_door (val ig : Unit = Unit) : location () ;

typealias loc_row = Array<location> ;
typealias loc_map = Array<loc_row> ;

fun loc_row_count (lr : loc_row, l : location) : Int {
  var result = 0 ;
  for (l_ in lr) {
    if (l_ == l) { result += 1 ; }
  }

  return result ;
}

fun loc_map_count (lm : loc_map, l : location) : Int {
  var result = 0 ;
  for (lr in lm) {
    result += loc_row_count (lr, l) ;
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

  val c2 = loc_map_count (lm, loc_player ()) == 1 ;
  val c3 = 1 <= loc_map_count (lm, loc_door ()) ;

  return c1 && c2 && c3 ;
}

sealed class major_ui ;
data class ui_game (val ig : Unit = Unit) : major_ui () ;
data class ui_postgame (val ig : Unit = Unit) : major_ui () ;
data class ui_menu (val ig : Unit = Unit) : major_ui () ;
data class ui_designer (val ig : Unit = Unit) : major_ui () ;

sealed class app_state ;
data class appst_launched (val ig : Unit = Unit) : app_state () ;
data class appst_running (val ig : Unit = Unit) : app_state () ;

typealias map_index = Int ;
typealias is_visible = Boolean ;
typealias is_victorious = Boolean ;

sealed class timer_control ;
data class tc_activate (val ig : Unit = Unit) : timer_control () ;
data class tc_deactivate (val ig : Unit = Unit) : timer_control () ;
data class tc_pause (val ig : Unit = Unit) : timer_control () ;
data class tc_play (val ig : Unit = Unit) : timer_control () ;

typealias coords = Pair<Int, Int> ;

sealed class movement ;
data class mv_up (val ig : Unit = Unit) : movement () ;
data class mv_left (val ig : Unit = Unit) : movement () ;
data class mv_right (val ig : Unit = Unit) : movement () ;
data class mv_down (val ig : Unit = Unit) : movement () ;

fun main (s : Array<String>) {
  println ("hola") ;
}

