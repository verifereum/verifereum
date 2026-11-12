Theory vfmTest2120[no_sig_docs]
Ancestors vfmTestDefs2120
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2120_0.nsv", "result2120_1.nsv", "result2120_2.nsv", "result2120_3.nsv", "result2120_4.nsv", "result2120_5.nsv", "result2120_6.nsv", "result2120_7.nsv", "result2120_8.nsv", "result2120_9.nsv"];
val thyn = "vfmTestDefs2120";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
