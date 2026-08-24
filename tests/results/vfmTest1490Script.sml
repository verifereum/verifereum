Theory vfmTest1490[no_sig_docs]
Ancestors vfmTestDefs1490
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1490_0.nsv"];
val thyn = "vfmTestDefs1490";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
