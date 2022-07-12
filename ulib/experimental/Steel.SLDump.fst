module Steel.SLDump

let sldump' #opened p text sq () =
  noop ()

let sldump #opened #p text #sq () =
  sldump' #opened p text sq ()
