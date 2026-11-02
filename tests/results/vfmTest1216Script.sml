Theory vfmTest1216[no_sig_docs]
Ancestors vfmTestDefs1216
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1216_0.nsv", "result1216_1.nsv", "result1216_2.nsv", "result1216_3.nsv", "result1216_4.nsv", "result1216_5.nsv", "result1216_6.nsv", "result1216_7.nsv", "result1216_8.nsv", "result1216_9.nsv", "result1216_10.nsv", "result1216_11.nsv", "result1216_12.nsv", "result1216_13.nsv", "result1216_14.nsv", "result1216_15.nsv", "result1216_16.nsv", "result1216_17.nsv", "result1216_18.nsv", "result1216_19.nsv", "result1216_20.nsv", "result1216_21.nsv", "result1216_22.nsv", "result1216_23.nsv", "result1216_24.nsv", "result1216_25.nsv", "result1216_26.nsv", "result1216_27.nsv", "result1216_28.nsv", "result1216_29.nsv", "result1216_30.nsv", "result1216_31.nsv", "result1216_32.nsv", "result1216_33.nsv", "result1216_34.nsv", "result1216_35.nsv", "result1216_36.nsv", "result1216_37.nsv", "result1216_38.nsv", "result1216_39.nsv", "result1216_40.nsv", "result1216_41.nsv", "result1216_42.nsv", "result1216_43.nsv", "result1216_44.nsv", "result1216_45.nsv", "result1216_46.nsv", "result1216_47.nsv", "result1216_48.nsv", "result1216_49.nsv", "result1216_50.nsv", "result1216_51.nsv", "result1216_52.nsv", "result1216_53.nsv", "result1216_54.nsv", "result1216_55.nsv", "result1216_56.nsv", "result1216_57.nsv", "result1216_58.nsv", "result1216_59.nsv", "result1216_60.nsv", "result1216_61.nsv"];
val thyn = "vfmTestDefs1216";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
