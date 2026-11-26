Theory vfmTest1505[no_sig_docs]
Ancestors vfmTestDefs1505
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1505_0.nsv", "result1505_1.nsv", "result1505_2.nsv", "result1505_3.nsv", "result1505_4.nsv", "result1505_5.nsv", "result1505_6.nsv", "result1505_7.nsv", "result1505_8.nsv", "result1505_9.nsv", "result1505_10.nsv", "result1505_11.nsv", "result1505_12.nsv", "result1505_13.nsv", "result1505_14.nsv", "result1505_15.nsv", "result1505_16.nsv", "result1505_17.nsv", "result1505_18.nsv", "result1505_19.nsv", "result1505_20.nsv", "result1505_21.nsv", "result1505_22.nsv", "result1505_23.nsv"];
val thyn = "vfmTestDefs1505";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
