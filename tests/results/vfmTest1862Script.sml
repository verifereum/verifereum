Theory vfmTest1862[no_sig_docs]
Ancestors vfmTestDefs1862
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1862_0.nsv", "result1862_1.nsv"];
val thyn = "vfmTestDefs1862";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
