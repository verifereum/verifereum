Theory vfmTest1531[no_sig_docs]
Ancestors vfmTestDefs1531
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1531_0.nsv", "result1531_1.nsv", "result1531_2.nsv", "result1531_3.nsv"];
val thyn = "vfmTestDefs1531";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
