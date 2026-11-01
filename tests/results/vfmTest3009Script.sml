Theory vfmTest3009[no_sig_docs]
Ancestors vfmTestDefs3009
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3009_0.nsv", "result3009_1.nsv", "result3009_2.nsv", "result3009_3.nsv", "result3009_4.nsv", "result3009_5.nsv", "result3009_6.nsv", "result3009_7.nsv", "result3009_8.nsv", "result3009_9.nsv", "result3009_10.nsv", "result3009_11.nsv", "result3009_12.nsv", "result3009_13.nsv", "result3009_14.nsv", "result3009_15.nsv", "result3009_16.nsv", "result3009_17.nsv", "result3009_18.nsv", "result3009_19.nsv", "result3009_20.nsv", "result3009_21.nsv", "result3009_22.nsv", "result3009_23.nsv", "result3009_24.nsv", "result3009_25.nsv", "result3009_26.nsv", "result3009_27.nsv", "result3009_28.nsv", "result3009_29.nsv", "result3009_30.nsv", "result3009_31.nsv", "result3009_32.nsv", "result3009_33.nsv", "result3009_34.nsv", "result3009_35.nsv", "result3009_36.nsv", "result3009_37.nsv", "result3009_38.nsv", "result3009_39.nsv", "result3009_40.nsv", "result3009_41.nsv", "result3009_42.nsv", "result3009_43.nsv", "result3009_44.nsv", "result3009_45.nsv", "result3009_46.nsv", "result3009_47.nsv", "result3009_48.nsv", "result3009_49.nsv", "result3009_50.nsv", "result3009_51.nsv", "result3009_52.nsv", "result3009_53.nsv", "result3009_54.nsv", "result3009_55.nsv"];
val thyn = "vfmTestDefs3009";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
