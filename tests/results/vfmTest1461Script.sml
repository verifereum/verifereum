Theory vfmTest1461[no_sig_docs]
Ancestors vfmTestDefs1461
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1461_0.nsv", "result1461_1.nsv", "result1461_2.nsv", "result1461_3.nsv", "result1461_4.nsv", "result1461_5.nsv", "result1461_6.nsv", "result1461_7.nsv", "result1461_8.nsv", "result1461_9.nsv"];
val thyn = "vfmTestDefs1461";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
