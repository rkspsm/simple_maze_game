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

Inductive movement :=
| mv_up
| mv_left
| mv_right
| mv_down
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
| game
| postgame
| menu
| designer
.

Inductive app_state :=
| app_launched
| app_running : major_ui -> app_state.

Definition is_visible := bool.
Definition is_victorious := bool.
    
Inductive command :=
| cmd_set_visibility : major_ui -> is_visible -> command
| cmd_set_postgame : is_victorious -> command
.
