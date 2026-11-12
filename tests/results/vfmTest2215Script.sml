Theory vfmTest2215[no_sig_docs]
Ancestors vfmTestDefs2215
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2215_0.nsv", "result2215_1.nsv", "result2215_2.nsv", "result2215_3.nsv", "result2215_4.nsv", "result2215_5.nsv", "result2215_6.nsv", "result2215_7.nsv", "result2215_8.nsv", "result2215_9.nsv", "result2215_10.nsv", "result2215_11.nsv", "result2215_12.nsv", "result2215_13.nsv", "result2215_14.nsv", "result2215_15.nsv", "result2215_16.nsv", "result2215_17.nsv", "result2215_18.nsv", "result2215_19.nsv", "result2215_20.nsv", "result2215_21.nsv", "result2215_22.nsv", "result2215_23.nsv", "result2215_24.nsv", "result2215_25.nsv", "result2215_26.nsv", "result2215_27.nsv", "result2215_28.nsv", "result2215_29.nsv", "result2215_30.nsv", "result2215_31.nsv", "result2215_32.nsv", "result2215_33.nsv", "result2215_34.nsv", "result2215_35.nsv", "result2215_36.nsv", "result2215_37.nsv", "result2215_38.nsv", "result2215_39.nsv", "result2215_40.nsv", "result2215_41.nsv", "result2215_42.nsv", "result2215_43.nsv", "result2215_44.nsv", "result2215_45.nsv", "result2215_46.nsv", "result2215_47.nsv", "result2215_48.nsv", "result2215_49.nsv", "result2215_50.nsv", "result2215_51.nsv", "result2215_52.nsv", "result2215_53.nsv", "result2215_54.nsv", "result2215_55.nsv", "result2215_56.nsv", "result2215_57.nsv", "result2215_58.nsv", "result2215_59.nsv"];
val thyn = "vfmTestDefs2215";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
