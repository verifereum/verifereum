Theory vfmTest1183[no_sig_docs]
Ancestors vfmTestDefs1183
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1183_0.nsv", "result1183_1.nsv", "result1183_2.nsv", "result1183_3.nsv", "result1183_4.nsv", "result1183_5.nsv", "result1183_6.nsv", "result1183_7.nsv", "result1183_8.nsv", "result1183_9.nsv", "result1183_10.nsv", "result1183_11.nsv", "result1183_12.nsv", "result1183_13.nsv", "result1183_14.nsv", "result1183_15.nsv", "result1183_16.nsv", "result1183_17.nsv", "result1183_18.nsv", "result1183_19.nsv", "result1183_20.nsv", "result1183_21.nsv", "result1183_22.nsv", "result1183_23.nsv", "result1183_24.nsv", "result1183_25.nsv", "result1183_26.nsv", "result1183_27.nsv", "result1183_28.nsv", "result1183_29.nsv", "result1183_30.nsv", "result1183_31.nsv", "result1183_32.nsv", "result1183_33.nsv", "result1183_34.nsv", "result1183_35.nsv", "result1183_36.nsv", "result1183_37.nsv", "result1183_38.nsv", "result1183_39.nsv", "result1183_40.nsv", "result1183_41.nsv", "result1183_42.nsv", "result1183_43.nsv", "result1183_44.nsv", "result1183_45.nsv", "result1183_46.nsv", "result1183_47.nsv", "result1183_48.nsv", "result1183_49.nsv", "result1183_50.nsv", "result1183_51.nsv", "result1183_52.nsv", "result1183_53.nsv", "result1183_54.nsv", "result1183_55.nsv"];
val thyn = "vfmTestDefs1183";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
