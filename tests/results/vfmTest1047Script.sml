Theory vfmTest1047[no_sig_docs]
Ancestors vfmTestDefs1047
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1047_0.nsv", "result1047_1.nsv", "result1047_2.nsv", "result1047_3.nsv", "result1047_4.nsv", "result1047_5.nsv", "result1047_6.nsv", "result1047_7.nsv", "result1047_8.nsv", "result1047_9.nsv", "result1047_10.nsv", "result1047_11.nsv", "result1047_12.nsv", "result1047_13.nsv", "result1047_14.nsv", "result1047_15.nsv", "result1047_16.nsv", "result1047_17.nsv", "result1047_18.nsv", "result1047_19.nsv", "result1047_20.nsv", "result1047_21.nsv", "result1047_22.nsv", "result1047_23.nsv", "result1047_24.nsv", "result1047_25.nsv", "result1047_26.nsv", "result1047_27.nsv", "result1047_28.nsv", "result1047_29.nsv", "result1047_30.nsv", "result1047_31.nsv", "result1047_32.nsv", "result1047_33.nsv", "result1047_34.nsv", "result1047_35.nsv", "result1047_36.nsv", "result1047_37.nsv", "result1047_38.nsv", "result1047_39.nsv", "result1047_40.nsv", "result1047_41.nsv", "result1047_42.nsv", "result1047_43.nsv", "result1047_44.nsv", "result1047_45.nsv", "result1047_46.nsv", "result1047_47.nsv"];
val thyn = "vfmTestDefs1047";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
