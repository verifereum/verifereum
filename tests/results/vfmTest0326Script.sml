Theory vfmTest0326[no_sig_docs]
Ancestors vfmTestDefs0326
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0326_0.nsv", "result0326_1.nsv", "result0326_2.nsv", "result0326_3.nsv", "result0326_4.nsv", "result0326_5.nsv", "result0326_6.nsv", "result0326_7.nsv", "result0326_8.nsv", "result0326_9.nsv", "result0326_10.nsv", "result0326_11.nsv", "result0326_12.nsv", "result0326_13.nsv", "result0326_14.nsv", "result0326_15.nsv", "result0326_16.nsv", "result0326_17.nsv", "result0326_18.nsv", "result0326_19.nsv", "result0326_20.nsv", "result0326_21.nsv", "result0326_22.nsv", "result0326_23.nsv", "result0326_24.nsv", "result0326_25.nsv", "result0326_26.nsv", "result0326_27.nsv", "result0326_28.nsv", "result0326_29.nsv", "result0326_30.nsv", "result0326_31.nsv", "result0326_32.nsv", "result0326_33.nsv", "result0326_34.nsv", "result0326_35.nsv", "result0326_36.nsv", "result0326_37.nsv", "result0326_38.nsv", "result0326_39.nsv", "result0326_40.nsv", "result0326_41.nsv", "result0326_42.nsv", "result0326_43.nsv", "result0326_44.nsv", "result0326_45.nsv"];
val thyn = "vfmTestDefs0326";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
