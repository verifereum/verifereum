Theory vfmTest1633[no_sig_docs]
Ancestors vfmTestDefs1633
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1633_0.nsv", "result1633_1.nsv", "result1633_2.nsv", "result1633_3.nsv", "result1633_4.nsv", "result1633_5.nsv", "result1633_6.nsv", "result1633_7.nsv", "result1633_8.nsv", "result1633_9.nsv", "result1633_10.nsv", "result1633_11.nsv", "result1633_12.nsv", "result1633_13.nsv", "result1633_14.nsv", "result1633_15.nsv"];
val thyn = "vfmTestDefs1633";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
