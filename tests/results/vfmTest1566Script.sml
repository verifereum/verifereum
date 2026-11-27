Theory vfmTest1566[no_sig_docs]
Ancestors vfmTestDefs1566
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1566_0.nsv", "result1566_1.nsv", "result1566_2.nsv", "result1566_3.nsv", "result1566_4.nsv", "result1566_5.nsv", "result1566_6.nsv", "result1566_7.nsv", "result1566_8.nsv", "result1566_9.nsv", "result1566_10.nsv", "result1566_11.nsv", "result1566_12.nsv", "result1566_13.nsv", "result1566_14.nsv", "result1566_15.nsv", "result1566_16.nsv", "result1566_17.nsv", "result1566_18.nsv", "result1566_19.nsv"];
val thyn = "vfmTestDefs1566";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
