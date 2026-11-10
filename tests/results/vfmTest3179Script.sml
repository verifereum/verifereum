Theory vfmTest3179[no_sig_docs]
Ancestors vfmTestDefs3179
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3179_0.nsv", "result3179_1.nsv", "result3179_2.nsv", "result3179_3.nsv", "result3179_4.nsv", "result3179_5.nsv", "result3179_6.nsv", "result3179_7.nsv", "result3179_8.nsv", "result3179_9.nsv", "result3179_10.nsv", "result3179_11.nsv", "result3179_12.nsv", "result3179_13.nsv", "result3179_14.nsv", "result3179_15.nsv", "result3179_16.nsv", "result3179_17.nsv", "result3179_18.nsv", "result3179_19.nsv", "result3179_20.nsv", "result3179_21.nsv", "result3179_22.nsv", "result3179_23.nsv", "result3179_24.nsv", "result3179_25.nsv", "result3179_26.nsv", "result3179_27.nsv", "result3179_28.nsv", "result3179_29.nsv", "result3179_30.nsv", "result3179_31.nsv", "result3179_32.nsv", "result3179_33.nsv", "result3179_34.nsv", "result3179_35.nsv", "result3179_36.nsv", "result3179_37.nsv", "result3179_38.nsv", "result3179_39.nsv", "result3179_40.nsv", "result3179_41.nsv", "result3179_42.nsv", "result3179_43.nsv", "result3179_44.nsv", "result3179_45.nsv", "result3179_46.nsv", "result3179_47.nsv", "result3179_48.nsv", "result3179_49.nsv", "result3179_50.nsv", "result3179_51.nsv", "result3179_52.nsv", "result3179_53.nsv", "result3179_54.nsv", "result3179_55.nsv"];
val thyn = "vfmTestDefs3179";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
