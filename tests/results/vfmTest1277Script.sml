Theory vfmTest1277[no_sig_docs]
Ancestors vfmTestDefs1277
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1277_0.nsv", "result1277_1.nsv", "result1277_2.nsv", "result1277_3.nsv", "result1277_4.nsv", "result1277_5.nsv", "result1277_6.nsv", "result1277_7.nsv", "result1277_8.nsv", "result1277_9.nsv", "result1277_10.nsv", "result1277_11.nsv", "result1277_12.nsv", "result1277_13.nsv", "result1277_14.nsv", "result1277_15.nsv", "result1277_16.nsv", "result1277_17.nsv", "result1277_18.nsv", "result1277_19.nsv", "result1277_20.nsv", "result1277_21.nsv", "result1277_22.nsv", "result1277_23.nsv", "result1277_24.nsv", "result1277_25.nsv", "result1277_26.nsv"];
val thyn = "vfmTestDefs1277";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
