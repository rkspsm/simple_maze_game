'use strict' ;

function verify_ext_level (data, loc_string, arr_board, obj_level) {
  if (data.what !== "level") { return null ; }
  if (! R.is (Number, data.rows)) { return null ; }
  if (! R.is (Number, data.cols)) { return null ; }

  const rows = parseInt (data.rows) ;
  const cols = parseInt (data.cols) ;

  if (! R.is (Object, data.board)) { return null ; }
  if (data.board.length !== rows) { return null ; }
  if (rows <= 0) { return null ; }

  const board = data.board

  const res_board = [] ;

  for (var ir = 0 ; ir < rows ; ir++) {
    const row = board[ir] ;
    const res_row = [] ;
    res_board.push (res_row) ;

    if (! R.is (Object, row)) { return null ; }
    if (row.length !== cols)) { return null ; }

    for (var ic = 0 ; ic < cols ; ic ++) {
      const rawval = row[i] ;
      if (! R.is (String, rawval)) { return null ; }
      const locval = loc_string (rawval) ;
      if (R.isNil (locval)) { return null ; }
      res_board.push (locval) ;
  }
}

