Theory vfmTest1364[no_sig_docs]
Ancestors vfmTestDefs1364
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1364_0.nsv"];
val thyn = "vfmTestDefs1364";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
