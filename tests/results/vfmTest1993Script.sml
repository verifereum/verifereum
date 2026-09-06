Theory vfmTest1993[no_sig_docs]
Ancestors vfmTestDefs1993
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1993_0.nsv", "result1993_1.nsv"];
val thyn = "vfmTestDefs1993";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
