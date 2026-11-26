Theory vfmTest1525[no_sig_docs]
Ancestors vfmTestDefs1525
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1525_0.nsv", "result1525_1.nsv", "result1525_2.nsv", "result1525_3.nsv", "result1525_4.nsv", "result1525_5.nsv", "result1525_6.nsv", "result1525_7.nsv", "result1525_8.nsv", "result1525_9.nsv", "result1525_10.nsv", "result1525_11.nsv", "result1525_12.nsv", "result1525_13.nsv", "result1525_14.nsv", "result1525_15.nsv", "result1525_16.nsv", "result1525_17.nsv", "result1525_18.nsv", "result1525_19.nsv", "result1525_20.nsv", "result1525_21.nsv", "result1525_22.nsv", "result1525_23.nsv", "result1525_24.nsv", "result1525_25.nsv", "result1525_26.nsv", "result1525_27.nsv", "result1525_28.nsv", "result1525_29.nsv", "result1525_30.nsv", "result1525_31.nsv"];
val thyn = "vfmTestDefs1525";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
