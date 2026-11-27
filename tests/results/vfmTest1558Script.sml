Theory vfmTest1558[no_sig_docs]
Ancestors vfmTestDefs1558
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1558_0.nsv", "result1558_1.nsv", "result1558_2.nsv", "result1558_3.nsv", "result1558_4.nsv", "result1558_5.nsv", "result1558_6.nsv", "result1558_7.nsv", "result1558_8.nsv"];
val thyn = "vfmTestDefs1558";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
