Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Bool.
Require Setoid.

Inductive location :=
| loc_empty
| loc_player
| loc_wall
| loc_key
| loc_door
.

Definition loc_map := list (list location).

Parameter loc_map_count : loc_map -> location -> nat.

Definition loc_map_valid (lm : loc_map) : Prop :=
  (forall l1 l2, In l1 lm -> In l2 lm -> length l1 = length l2) /\
  (loc_map_count lm loc_player = 1) /\
  (1 <= loc_map_count lm loc_door).

Inductive major_ui :=
| ui_game
| ui_postgame
| ui_menu
| ui_designer
| ui_replay
.

Parameter map_index : Set.

Definition is_victorious := bool.
Definition is_paused := bool.

Inductive app_state :=
| appst_launched
| appst_game : is_paused -> app_state
| appst_postgame : is_victorious -> app_state
| appst_menu
| appst_designer
| appst_replay
.

Inductive timer_control :=
| tc_reset
| tc_run
| tc_stop
| tc_pause
.

Definition coords := (prod nat nat).

Inductive movement :=
| mv_up
| mv_left
| mv_right
| mv_down
.
    
Inductive command :=
| cmd_set_state : app_state -> command
| cmd_select_ui : major_ui -> command
| cmd_set_postgame : is_victorious -> command
| cmd_game_timer : timer_control -> command
| cmd_game_pause : bool -> command
| cmd_select_map : map_index -> command
| cmd_game_fuel_tick
| cmd_game_process_move
.

Inductive stimulus :=
| stls_launched
| stls_game_moved : movement -> stimulus
| stls_menu_map_selected : map_index -> stimulus
| stls_postgame_goto_menu
| stls_postgame_play_again
| stls_menu_designer
| stls_game_tick
| stls_game_pause : bool -> stimulus
| stls_game_quit
| stls_game_fuel_empty
.

Inductive process : app_state -> stimulus -> list command -> Prop :=

| proc_launched :
    process appst_launched stls_launched
            [ cmd_set_state appst_menu ;
                cmd_select_ui ui_menu
            ]

| proc_menu_map_selected : forall mi,
    process appst_menu (stls_menu_map_selected mi)
            [ cmd_select_map mi ;
                cmd_select_ui ui_game ;
                cmd_game_timer tc_reset ;
                cmd_game_timer tc_run ;
                cmd_set_state (appst_game false)
            ]

| proc_game_tick :
    process (appst_game false) stls_game_tick
            [ cmd_game_fuel_tick ]

| proc_game_paused :
    process (appst_game false) (stls_game_pause true)
            [ cmd_game_timer tc_pause ;
                cmd_set_state (appst_game true)
            ]

| proc_game_resumed :
    process (appst_game true) (stls_game_pause false)
            [ cmd_game_timer tc_run ;
                cmd_set_state (appst_game false)
            ]

| proc_game_move : forall m,
    process (appst_game false) (stls_game_moved m)
            [ cmd_game_process_move ]
.

Inductive move_command :=
| mvcmd_update_coords : coords -> location -> move_command
| mvcmd_update_doors
| mvcmd_trigger_victory
| mvcmd_expend_fuel
| mvcmd_update_player_coords
.

Parameter move_within_bounds : forall (src : coords) (m : movement) (dest : coords), Prop.
Parameter map_location : forall (m : loc_map) (c : coords) (l : location), Prop.

Inductive process_move : loc_map -> coords -> movement -> list move_command -> Prop :=

| pmv_to_empty : forall board src mv _dest,
    move_within_bounds src mv _dest ->
    map_location board _dest loc_empty ->
    process_move board src mv
                 [ mvcmd_expend_fuel ;
                     mvcmd_update_coords src loc_empty ;
                     mvcmd_update_coords _dest loc_player ;
                     mvcmd_update_player_coords _dest
                 ]

| pmv_to_key : forall board src mv _dest,
    move_within_bounds src mv _dest ->
    map_location board _dest loc_key ->
.
