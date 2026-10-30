Theory vfmTest1093[no_sig_docs]
Ancestors vfmTestDefs1093
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1093_0.nsv", "result1093_1.nsv", "result1093_2.nsv", "result1093_3.nsv", "result1093_4.nsv", "result1093_5.nsv", "result1093_6.nsv", "result1093_7.nsv", "result1093_8.nsv", "result1093_9.nsv", "result1093_10.nsv", "result1093_11.nsv", "result1093_12.nsv", "result1093_13.nsv", "result1093_14.nsv", "result1093_15.nsv", "result1093_16.nsv", "result1093_17.nsv", "result1093_18.nsv", "result1093_19.nsv", "result1093_20.nsv", "result1093_21.nsv", "result1093_22.nsv", "result1093_23.nsv", "result1093_24.nsv", "result1093_25.nsv", "result1093_26.nsv", "result1093_27.nsv", "result1093_28.nsv", "result1093_29.nsv", "result1093_30.nsv", "result1093_31.nsv", "result1093_32.nsv", "result1093_33.nsv", "result1093_34.nsv", "result1093_35.nsv", "result1093_36.nsv", "result1093_37.nsv", "result1093_38.nsv", "result1093_39.nsv", "result1093_40.nsv", "result1093_41.nsv", "result1093_42.nsv", "result1093_43.nsv", "result1093_44.nsv", "result1093_45.nsv"];
val thyn = "vfmTestDefs1093";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
