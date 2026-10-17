Theory vfmTest1631[no_sig_docs]
Ancestors vfmTestDefs1631
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1631_0.nsv", "result1631_1.nsv", "result1631_2.nsv", "result1631_3.nsv", "result1631_4.nsv", "result1631_5.nsv", "result1631_6.nsv", "result1631_7.nsv", "result1631_8.nsv", "result1631_9.nsv", "result1631_10.nsv", "result1631_11.nsv", "result1631_12.nsv", "result1631_13.nsv", "result1631_14.nsv", "result1631_15.nsv", "result1631_16.nsv", "result1631_17.nsv", "result1631_18.nsv", "result1631_19.nsv", "result1631_20.nsv", "result1631_21.nsv", "result1631_22.nsv", "result1631_23.nsv", "result1631_24.nsv", "result1631_25.nsv", "result1631_26.nsv", "result1631_27.nsv", "result1631_28.nsv", "result1631_29.nsv", "result1631_30.nsv", "result1631_31.nsv"];
val thyn = "vfmTestDefs1631";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
