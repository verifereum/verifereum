Theory vfmTest2088[no_sig_docs]
Ancestors vfmTestDefs2088
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2088_0.nsv", "result2088_1.nsv", "result2088_2.nsv", "result2088_3.nsv", "result2088_4.nsv", "result2088_5.nsv", "result2088_6.nsv", "result2088_7.nsv", "result2088_8.nsv", "result2088_9.nsv", "result2088_10.nsv", "result2088_11.nsv", "result2088_12.nsv", "result2088_13.nsv", "result2088_14.nsv"];
val thyn = "vfmTestDefs2088";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
