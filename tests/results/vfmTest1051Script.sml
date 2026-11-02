Theory vfmTest1051[no_sig_docs]
Ancestors vfmTestDefs1051
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1051_0.nsv", "result1051_1.nsv", "result1051_2.nsv", "result1051_3.nsv", "result1051_4.nsv", "result1051_5.nsv", "result1051_6.nsv", "result1051_7.nsv", "result1051_8.nsv"];
val thyn = "vfmTestDefs1051";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
