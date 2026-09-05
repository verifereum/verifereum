Theory vfmTest1625[no_sig_docs]
Ancestors vfmTestDefs1625
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1625_0.nsv", "result1625_1.nsv", "result1625_2.nsv", "result1625_3.nsv", "result1625_4.nsv", "result1625_5.nsv", "result1625_6.nsv", "result1625_7.nsv", "result1625_8.nsv", "result1625_9.nsv", "result1625_10.nsv", "result1625_11.nsv", "result1625_12.nsv", "result1625_13.nsv", "result1625_14.nsv", "result1625_15.nsv", "result1625_16.nsv", "result1625_17.nsv", "result1625_18.nsv", "result1625_19.nsv", "result1625_20.nsv", "result1625_21.nsv", "result1625_22.nsv", "result1625_23.nsv", "result1625_24.nsv", "result1625_25.nsv", "result1625_26.nsv", "result1625_27.nsv", "result1625_28.nsv", "result1625_29.nsv", "result1625_30.nsv", "result1625_31.nsv", "result1625_32.nsv", "result1625_33.nsv", "result1625_34.nsv", "result1625_35.nsv"];
val thyn = "vfmTestDefs1625";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
