Theory vfmTest1432[no_sig_docs]
Ancestors vfmTestDefs1432
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1432_0.nsv"];
val thyn = "vfmTestDefs1432";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
