Theory vfmTest1539[no_sig_docs]
Ancestors vfmTestDefs1539
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1539_0.nsv", "result1539_1.nsv", "result1539_2.nsv", "result1539_3.nsv", "result1539_4.nsv", "result1539_5.nsv", "result1539_6.nsv", "result1539_7.nsv", "result1539_8.nsv", "result1539_9.nsv", "result1539_10.nsv", "result1539_11.nsv", "result1539_12.nsv", "result1539_13.nsv", "result1539_14.nsv", "result1539_15.nsv", "result1539_16.nsv", "result1539_17.nsv", "result1539_18.nsv", "result1539_19.nsv"];
val thyn = "vfmTestDefs1539";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
