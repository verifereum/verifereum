Theory vfmTest1215[no_sig_docs]
Ancestors vfmTestDefs1215
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1215_0.nsv", "result1215_1.nsv", "result1215_2.nsv", "result1215_3.nsv", "result1215_4.nsv", "result1215_5.nsv", "result1215_6.nsv", "result1215_7.nsv", "result1215_8.nsv", "result1215_9.nsv", "result1215_10.nsv", "result1215_11.nsv", "result1215_12.nsv", "result1215_13.nsv", "result1215_14.nsv", "result1215_15.nsv", "result1215_16.nsv", "result1215_17.nsv", "result1215_18.nsv", "result1215_19.nsv", "result1215_20.nsv", "result1215_21.nsv", "result1215_22.nsv", "result1215_23.nsv", "result1215_24.nsv", "result1215_25.nsv", "result1215_26.nsv", "result1215_27.nsv", "result1215_28.nsv", "result1215_29.nsv", "result1215_30.nsv", "result1215_31.nsv", "result1215_32.nsv", "result1215_33.nsv", "result1215_34.nsv", "result1215_35.nsv", "result1215_36.nsv", "result1215_37.nsv", "result1215_38.nsv", "result1215_39.nsv", "result1215_40.nsv", "result1215_41.nsv", "result1215_42.nsv", "result1215_43.nsv", "result1215_44.nsv", "result1215_45.nsv", "result1215_46.nsv", "result1215_47.nsv", "result1215_48.nsv", "result1215_49.nsv", "result1215_50.nsv", "result1215_51.nsv"];
val thyn = "vfmTestDefs1215";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
