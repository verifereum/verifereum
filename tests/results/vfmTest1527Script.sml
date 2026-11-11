Theory vfmTest1527[no_sig_docs]
Ancestors vfmTestDefs1527
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1527_0.nsv", "result1527_1.nsv", "result1527_2.nsv", "result1527_3.nsv"];
val thyn = "vfmTestDefs1527";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
