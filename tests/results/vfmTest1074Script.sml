Theory vfmTest1074[no_sig_docs]
Ancestors vfmTestDefs1074
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1074_0.nsv", "result1074_1.nsv", "result1074_2.nsv", "result1074_3.nsv", "result1074_4.nsv", "result1074_5.nsv"];
val thyn = "vfmTestDefs1074";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
