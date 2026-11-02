Theory vfmTest2996[no_sig_docs]
Ancestors vfmTestDefs2996
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2996_0.nsv", "result2996_1.nsv", "result2996_2.nsv", "result2996_3.nsv", "result2996_4.nsv", "result2996_5.nsv", "result2996_6.nsv", "result2996_7.nsv", "result2996_8.nsv", "result2996_9.nsv", "result2996_10.nsv", "result2996_11.nsv", "result2996_12.nsv", "result2996_13.nsv", "result2996_14.nsv", "result2996_15.nsv", "result2996_16.nsv", "result2996_17.nsv", "result2996_18.nsv", "result2996_19.nsv", "result2996_20.nsv", "result2996_21.nsv", "result2996_22.nsv", "result2996_23.nsv", "result2996_24.nsv", "result2996_25.nsv", "result2996_26.nsv", "result2996_27.nsv", "result2996_28.nsv", "result2996_29.nsv", "result2996_30.nsv", "result2996_31.nsv", "result2996_32.nsv", "result2996_33.nsv", "result2996_34.nsv", "result2996_35.nsv", "result2996_36.nsv", "result2996_37.nsv", "result2996_38.nsv", "result2996_39.nsv", "result2996_40.nsv", "result2996_41.nsv", "result2996_42.nsv", "result2996_43.nsv", "result2996_44.nsv", "result2996_45.nsv", "result2996_46.nsv", "result2996_47.nsv", "result2996_48.nsv", "result2996_49.nsv", "result2996_50.nsv", "result2996_51.nsv", "result2996_52.nsv", "result2996_53.nsv", "result2996_54.nsv"];
val thyn = "vfmTestDefs2996";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
