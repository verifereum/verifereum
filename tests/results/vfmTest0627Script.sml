Theory vfmTest0627[no_sig_docs]
Ancestors vfmTestDefs0627
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0627_0.nsv"];
val thyn = "vfmTestDefs0627";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
