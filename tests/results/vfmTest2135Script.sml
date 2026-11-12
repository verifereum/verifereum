Theory vfmTest2135[no_sig_docs]
Ancestors vfmTestDefs2135
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2135_0.nsv", "result2135_1.nsv", "result2135_2.nsv", "result2135_3.nsv", "result2135_4.nsv", "result2135_5.nsv", "result2135_6.nsv", "result2135_7.nsv", "result2135_8.nsv", "result2135_9.nsv", "result2135_10.nsv", "result2135_11.nsv", "result2135_12.nsv", "result2135_13.nsv", "result2135_14.nsv", "result2135_15.nsv", "result2135_16.nsv", "result2135_17.nsv", "result2135_18.nsv", "result2135_19.nsv", "result2135_20.nsv", "result2135_21.nsv", "result2135_22.nsv", "result2135_23.nsv", "result2135_24.nsv", "result2135_25.nsv", "result2135_26.nsv", "result2135_27.nsv", "result2135_28.nsv", "result2135_29.nsv", "result2135_30.nsv", "result2135_31.nsv", "result2135_32.nsv", "result2135_33.nsv", "result2135_34.nsv", "result2135_35.nsv", "result2135_36.nsv", "result2135_37.nsv", "result2135_38.nsv", "result2135_39.nsv", "result2135_40.nsv", "result2135_41.nsv", "result2135_42.nsv", "result2135_43.nsv", "result2135_44.nsv", "result2135_45.nsv", "result2135_46.nsv", "result2135_47.nsv", "result2135_48.nsv", "result2135_49.nsv", "result2135_50.nsv", "result2135_51.nsv", "result2135_52.nsv", "result2135_53.nsv"];
val thyn = "vfmTestDefs2135";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
