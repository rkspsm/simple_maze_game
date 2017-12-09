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

Definition loc_row := list location.
Definition loc_map := list loc_row.

Definition beq_loc (l1 l2 : location) : bool :=
  match l1,l2 with
  | loc_empty, loc_empty => true
  | loc_player, loc_player => true
  | loc_wall, loc_wall => true
  | loc_key, loc_key => true
  | loc_door, loc_door => true
  | _,_ => false
  end.

Fixpoint loc_row_count (lr : loc_row) (l : location) : nat :=
  match lr with
  | nil => O
  | l' :: lr' => match (beq_loc l l') with
                 | true => S (loc_row_count lr' l)
                 | false => loc_row_count lr' l
                 end
  end.

Fixpoint loc_map_count (lm : loc_map) (l : location) : nat :=
  match lm with
  | nil => 0
  | lr' :: lm' => (loc_row_count lr' l) + (loc_map_count lm' l)
  end.

Definition loc_map_valid (lm : loc_map) : Prop :=
  (forall l1 l2, In l1 lm -> In l2 lm -> length l1 = length l2) /\
  (loc_map_count lm loc_player = 1) /\
  (1 <= loc_map_count lm loc_door).

Inductive major_ui :=
| ui_game
| ui_postgame
| ui_menu
| ui_designer
.

Inductive app_state :=
| appst_launched
| appst_running : major_ui -> app_state.

Parameter map_index : Set.

Definition is_visible := bool.
Definition is_victorious := bool.

Inductive timer_control :=
| tc_activate
| tc_deactivate
| tc_pause
| tc_play
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
| cmd_set_visibility : major_ui -> is_visible -> command
| cmd_set_postgame : is_victorious -> command
| cmd_game_timer_activate : timer_control -> command
| cmd_game_pause : bool -> command
| cmd_select_map : map_index -> command
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
.

Inductive process : app_state -> stimulus -> list command -> Prop :=.
