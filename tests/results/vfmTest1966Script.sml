Theory vfmTest1966[no_sig_docs]
Ancestors vfmTestDefs1966
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1966_0.nsv"];
val thyn = "vfmTestDefs1966";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
