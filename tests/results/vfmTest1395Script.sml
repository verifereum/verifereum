Theory vfmTest1395[no_sig_docs]
Ancestors vfmTestDefs1395
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1395_0.nsv", "result1395_1.nsv", "result1395_2.nsv", "result1395_3.nsv", "result1395_4.nsv", "result1395_5.nsv", "result1395_6.nsv", "result1395_7.nsv", "result1395_8.nsv", "result1395_9.nsv"];
val thyn = "vfmTestDefs1395";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
