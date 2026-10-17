Theory vfmTest1609[no_sig_docs]
Ancestors vfmTestDefs1609
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1609_0.nsv", "result1609_1.nsv", "result1609_2.nsv", "result1609_3.nsv", "result1609_4.nsv", "result1609_5.nsv", "result1609_6.nsv", "result1609_7.nsv", "result1609_8.nsv", "result1609_9.nsv", "result1609_10.nsv", "result1609_11.nsv", "result1609_12.nsv", "result1609_13.nsv", "result1609_14.nsv", "result1609_15.nsv", "result1609_16.nsv", "result1609_17.nsv", "result1609_18.nsv", "result1609_19.nsv", "result1609_20.nsv", "result1609_21.nsv", "result1609_22.nsv", "result1609_23.nsv", "result1609_24.nsv", "result1609_25.nsv", "result1609_26.nsv", "result1609_27.nsv", "result1609_28.nsv", "result1609_29.nsv", "result1609_30.nsv", "result1609_31.nsv", "result1609_32.nsv", "result1609_33.nsv", "result1609_34.nsv", "result1609_35.nsv"];
val thyn = "vfmTestDefs1609";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
