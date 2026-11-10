Theory vfmTest1185[no_sig_docs]
Ancestors vfmTestDefs1185
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1185_0.nsv", "result1185_1.nsv", "result1185_2.nsv", "result1185_3.nsv", "result1185_4.nsv", "result1185_5.nsv", "result1185_6.nsv", "result1185_7.nsv", "result1185_8.nsv", "result1185_9.nsv", "result1185_10.nsv", "result1185_11.nsv", "result1185_12.nsv", "result1185_13.nsv", "result1185_14.nsv", "result1185_15.nsv", "result1185_16.nsv", "result1185_17.nsv", "result1185_18.nsv", "result1185_19.nsv", "result1185_20.nsv", "result1185_21.nsv", "result1185_22.nsv", "result1185_23.nsv", "result1185_24.nsv", "result1185_25.nsv", "result1185_26.nsv", "result1185_27.nsv", "result1185_28.nsv", "result1185_29.nsv", "result1185_30.nsv", "result1185_31.nsv", "result1185_32.nsv", "result1185_33.nsv", "result1185_34.nsv", "result1185_35.nsv", "result1185_36.nsv", "result1185_37.nsv", "result1185_38.nsv", "result1185_39.nsv", "result1185_40.nsv", "result1185_41.nsv", "result1185_42.nsv", "result1185_43.nsv", "result1185_44.nsv", "result1185_45.nsv"];
val thyn = "vfmTestDefs1185";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
