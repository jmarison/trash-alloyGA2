var sig File {}
var sig Trash in File {}

fact init {
  no Trash
}

pred empty {
  some Trash and       // guard
  after no Trash and   // effect on Trash
  File' = File - Trash // effect on File
}

pred delete [f : File] {
  not (f in Trash)   // guard
  Trash' = Trash + f // effect on Trash
  File' = File      // frame condition on File
}

pred directDelete[f : File]{
    not (f in Trash)
    Trash' = Trash
    File' = File - f
}


pred restore [f : File] {
  f in Trash         // guard
  Trash' = Trash - f // effect on Trash
  File' = File       // frame condition on File
}
assert restore_after_delete{
  always (all f: File | restore[f] implies once delete[f])
}

assert delete_all{
  always ((Trash = File and empty) implies always no File)
}

fact trans {
  always (empty or (some f : File | delete[f] or restore[f] or directDelete[f]))
}
check restore_after_delete for 5 but 20 steps

check delete_all
run no_files {
  some File
  eventually no File
  } for 5


  run example{}
