Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Bool.
Require Setoid.

Inductive Mutable (A:Set) : Set :=
| mutable : forall (a:A), Mutable A
.

Arguments mutable {A} _.

Definition copy_extract {A:Set} (x: @Mutable A) : A :=
  match x with
  | mutable x' => x'
  end.

Arguments mutable {A} _.

Parameter Immutable : Set -> Prop.

Definition is_opened := bool.
Definition is_opened_true := true.
Definition is_opened_false := false.

Inductive location :=
| loc_empty
| loc_player
| loc_wall
| loc_key
| loc_door : is_opened -> location
.

Definition loc_map := list (list location).
Parameter copy_loc_map : Immutable loc_map -> Mutable loc_map.

Parameter loc_map_count : loc_map -> location -> nat.

Definition loc_map_valid (lm : loc_map) : Prop :=
  (forall l1 l2, In l1 lm -> In l2 lm -> length l1 = length l2) /\
  (loc_map_count lm loc_player = 1) /\
  (1 <= (loc_map_count lm (loc_door is_opened_true)) + (loc_map_count lm (loc_door is_opened_false))).

Inductive major_ui :=
| ui_game
| ui_postgame
| ui_menu
| ui_designer
| ui_replay
.

Definition is_victorious := bool.
Definition is_paused := bool.

Definition is_paused_true := true.
Definition is_paused_false := false.
Definition is_victorious_true := true.
Definition is_victorious_false := false.

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

Parameter game_time : Set.
Parameter gt_minus : game_time -> game_time -> game_time.
Parameter game_fuel : Set.

Definition location_update := (prod coords location).
Definition location_updates := list location_update.

Inductive move_command :=
| mvcmd_update_coords : coords -> location -> move_command
| mvcmd_key_update_doors
| mvcmd_trigger_victory
| mvcmd_expend_fuel
| mvcmd_update_player_coords : coords -> move_command
| mvcmd_append_to_replay : location_updates -> move_command
| mvcmd_add_fuel : coords -> move_command
.

Parameter move_within_bounds : forall (board : loc_map) (src : coords) (m : movement) (dest : coords), Prop.
Parameter map_location : forall (m : loc_map) (c : coords) (l : location), Prop.

Inductive process_move : loc_map -> coords -> movement -> list move_command -> Prop :=

| pmv_to_empty : forall board src mv _dest,
    move_within_bounds board src mv _dest ->
    map_location board _dest loc_empty ->
    process_move board src mv
                 [ mvcmd_update_coords src loc_empty ;
                     mvcmd_update_coords _dest loc_player ;
                     mvcmd_update_player_coords _dest ;
                     mvcmd_expend_fuel ;
                     mvcmd_append_to_replay
                       [ (src, loc_empty) ; (_dest, loc_player) ]
                 ]

| pmv_to_key : forall board src mv _dest,
    move_within_bounds board src mv _dest ->
    map_location board _dest loc_key ->
    process_move board src mv
                 [ mvcmd_update_coords src loc_empty ;
                     mvcmd_update_coords _dest loc_player ;
                     mvcmd_update_player_coords _dest ;
                     mvcmd_key_update_doors ;
                     mvcmd_add_fuel _dest ;
                     mvcmd_append_to_replay
                       [ (src, loc_empty) ; (_dest, loc_player) ]
                 ]

| pmv_to_opened_door : forall board src mv _dest,
    move_within_bounds board src mv _dest ->
    map_location board _dest (loc_door is_opened_true) ->
    process_move board src mv
                 [ mvcmd_update_coords src loc_empty ;
                     mvcmd_update_coords _dest loc_player ;
                     mvcmd_update_player_coords _dest ;
                     mvcmd_append_to_replay
                       [ (src, loc_empty) ; (_dest, loc_player) ] ;
                     mvcmd_trigger_victory
                 ]
.

Inductive replay_command :=
| rcmd_init : game_time -> replay_command
| rcmd_loc_update : game_time -> location_updates -> replay_command
| rcmd_fuel_update : game_time -> game_fuel -> replay_command
| rcmd_finish : game_time -> is_victorious -> replay_command
| rcmd_abort : game_time -> replay_command
.

Parameter replay_context :
  (Mutable game_fuel) -> game_time -> Prop.

Inductive relproc_move_replay :
  move_command -> list replay_command -> Prop :=

| rmr_append_to_replay : forall fuel gt lups,
    replay_context fuel gt ->
    relproc_move_replay (mvcmd_append_to_replay lups)
                        [ rcmd_fuel_update gt (copy_extract fuel) ;
                            rcmd_loc_update gt lups
                        ]
.

Parameter level_index : Set.

Inductive stimulus :=
| stls_launched
    
| stls_menu_level_selected : level_index -> stimulus
| stls_menu_designer
| stls_menu_replay
| stls_menu_game_info
    
| stls_game_moved : movement -> stimulus
| stls_game_tick
| stls_game_pause : bool -> stimulus
| stls_game_quit
| stls_game_victory
| stls_game_fuel_empty
                                          
| stls_postgame_goto_menu
| stls_postgame_play_again
| stls_postgame_download_replay
.

Inductive command :=
| cmd_set_state : app_state -> command
| cmd_select_ui : major_ui -> command
| cmd_set_postgame : is_victorious -> command
| cmd_select_level : level_index -> command
| cmd_reset_map
| cmd_fetch_builtin_level_populate_menu

| cmd_game_timer : timer_control -> command
| cmd_game_pause : bool -> command
| cmd_game_fuel_tick
| cmd_game_process_move : movement -> command
| cmd_game_init_replay
| cmd_game_finish_replay : option is_victorious -> command

| cmd_postgame_prepare_replay
| cmd_postgame_offer_replay_download
.

Inductive process : app_state -> stimulus -> list command -> Prop :=

| proc_launched :
    process appst_launched stls_launched
            [ cmd_set_state appst_menu ;
                cmd_select_ui ui_menu ;
                cmd_fetch_builtin_level_populate_menu
            ]

| proc_menu_map_selected : forall li,
    process appst_menu (stls_menu_level_selected li)
            [ cmd_select_level li ;
                cmd_select_ui ui_game ;
                cmd_game_timer tc_reset ;
                cmd_game_timer tc_run ;
                cmd_set_state (appst_game false) ;
                cmd_game_init_replay
            ]

| proc_game_tick :
    process (appst_game is_paused_false) stls_game_tick
            [ cmd_game_fuel_tick ]

| proc_game_paused :
    process (appst_game is_paused_false) (stls_game_pause is_paused_true)
            [ cmd_game_timer tc_pause ;
                cmd_set_state (appst_game is_paused_true)
            ]

| proc_game_resumed :
    process (appst_game is_paused_true) (stls_game_pause is_paused_false)
            [ cmd_game_timer tc_run ;
                cmd_set_state (appst_game is_paused_false)
            ]

| proc_game_move : forall m,
    process (appst_game is_paused_false) (stls_game_moved m)
            [ cmd_game_process_move m ]

| proc_victory :
    process (appst_game is_paused_false) stls_game_victory
            [ cmd_set_state (appst_postgame is_victorious_true) ;
                cmd_game_finish_replay (Some is_victorious_true) ;
                cmd_game_timer tc_stop ;
                cmd_set_postgame is_victorious_true ;
                cmd_select_ui ui_postgame ;
                cmd_postgame_prepare_replay
            ]

| proc_fuel_empty :
    process (appst_game is_paused_false) stls_game_fuel_empty
            [ cmd_set_state (appst_postgame is_victorious_false) ;
                cmd_game_finish_replay (Some is_victorious_false) ;
                cmd_game_timer tc_stop ;
                cmd_set_postgame is_victorious_false ;
                cmd_select_ui ui_postgame ;
                cmd_postgame_prepare_replay
            ]

| proc_game_quit :
    process (appst_game is_paused_false) stls_game_fuel_empty
            [ cmd_set_state (appst_postgame is_victorious_false) ;
                cmd_game_finish_replay None ;
                cmd_game_timer tc_stop ;
                cmd_set_postgame is_victorious_false ;
                cmd_select_ui ui_postgame ;
                cmd_postgame_prepare_replay
            ]

| proc_postgame_goto_menu : forall is_vict,
    process (appst_postgame is_vict) stls_postgame_goto_menu
            [ cmd_set_state appst_menu ;
                cmd_select_ui ui_menu
            ]

| proc_postgame_play_again : forall is_vict,
    process (appst_postgame is_vict) stls_postgame_play_again
            [ cmd_reset_map ;
                cmd_set_state (appst_game is_paused_false) ;
                cmd_game_timer tc_reset ;
                cmd_game_timer tc_run ;
                cmd_select_ui ui_game ;
                cmd_game_init_replay
            ]

| proc_replay_download : forall is_vic,
    process (appst_postgame is_vic) stls_postgame_download_replay
            [ cmd_postgame_offer_replay_download ]
            
.

Inductive relproc_replay : command -> list replay_command -> Prop :=

| rr_init_replay : forall fuel gt,
    replay_context fuel gt ->
    relproc_replay cmd_game_init_replay
                   [ rcmd_init gt ]

| rr_win : forall gt fuel,
    replay_context fuel gt ->
    relproc_replay (cmd_game_finish_replay (Some is_victorious_true))
                   [ rcmd_finish gt is_victorious_true ]

| rr_loss : forall gt fuel,
    replay_context fuel gt ->
    relproc_replay (cmd_game_finish_replay (Some is_victorious_false))
                   [ rcmd_finish gt is_victorious_false ]

| rr_abort : forall gt fuel,
    replay_context fuel gt ->
    relproc_replay (cmd_game_finish_replay None)
                   [ rcmd_abort gt ]
.

Inductive level : Set :=
| new_level : forall
    (board : Immutable loc_map)
    (tick_interval : game_time)
    (max_fuel : game_fuel)
    (starting_fuel : game_fuel)
    (key_fuel : coords -> game_fuel)
    (door_keys : coords -> nat)
    (tick_cost : game_fuel)
    (move_cost : game_fuel),

    level.