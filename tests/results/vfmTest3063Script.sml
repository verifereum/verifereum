Theory vfmTest3063[no_sig_docs]
Ancestors vfmTestDefs3063
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3063_0.nsv", "result3063_1.nsv", "result3063_2.nsv", "result3063_3.nsv", "result3063_4.nsv", "result3063_5.nsv", "result3063_6.nsv", "result3063_7.nsv", "result3063_8.nsv", "result3063_9.nsv", "result3063_10.nsv", "result3063_11.nsv", "result3063_12.nsv", "result3063_13.nsv", "result3063_14.nsv", "result3063_15.nsv", "result3063_16.nsv", "result3063_17.nsv", "result3063_18.nsv", "result3063_19.nsv", "result3063_20.nsv", "result3063_21.nsv", "result3063_22.nsv", "result3063_23.nsv", "result3063_24.nsv", "result3063_25.nsv", "result3063_26.nsv", "result3063_27.nsv", "result3063_28.nsv", "result3063_29.nsv", "result3063_30.nsv", "result3063_31.nsv", "result3063_32.nsv", "result3063_33.nsv", "result3063_34.nsv", "result3063_35.nsv", "result3063_36.nsv", "result3063_37.nsv", "result3063_38.nsv", "result3063_39.nsv", "result3063_40.nsv", "result3063_41.nsv", "result3063_42.nsv", "result3063_43.nsv", "result3063_44.nsv", "result3063_45.nsv", "result3063_46.nsv", "result3063_47.nsv"];
val thyn = "vfmTestDefs3063";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
