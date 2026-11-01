Theory vfmTest1385[no_sig_docs]
Ancestors vfmTestDefs1385
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1385_0.nsv", "result1385_1.nsv", "result1385_2.nsv", "result1385_3.nsv", "result1385_4.nsv", "result1385_5.nsv", "result1385_6.nsv", "result1385_7.nsv", "result1385_8.nsv", "result1385_9.nsv", "result1385_10.nsv", "result1385_11.nsv"];
val thyn = "vfmTestDefs1385";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
