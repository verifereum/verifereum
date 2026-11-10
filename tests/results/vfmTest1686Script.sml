Theory vfmTest1686[no_sig_docs]
Ancestors vfmTestDefs1686
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1686_0.nsv", "result1686_1.nsv", "result1686_2.nsv", "result1686_3.nsv", "result1686_4.nsv", "result1686_5.nsv", "result1686_6.nsv", "result1686_7.nsv", "result1686_8.nsv", "result1686_9.nsv", "result1686_10.nsv", "result1686_11.nsv", "result1686_12.nsv", "result1686_13.nsv", "result1686_14.nsv", "result1686_15.nsv", "result1686_16.nsv", "result1686_17.nsv", "result1686_18.nsv", "result1686_19.nsv", "result1686_20.nsv", "result1686_21.nsv", "result1686_22.nsv", "result1686_23.nsv", "result1686_24.nsv", "result1686_25.nsv", "result1686_26.nsv", "result1686_27.nsv", "result1686_28.nsv", "result1686_29.nsv", "result1686_30.nsv", "result1686_31.nsv", "result1686_32.nsv", "result1686_33.nsv", "result1686_34.nsv", "result1686_35.nsv", "result1686_36.nsv", "result1686_37.nsv", "result1686_38.nsv", "result1686_39.nsv", "result1686_40.nsv", "result1686_41.nsv", "result1686_42.nsv", "result1686_43.nsv", "result1686_44.nsv", "result1686_45.nsv", "result1686_46.nsv", "result1686_47.nsv", "result1686_48.nsv", "result1686_49.nsv", "result1686_50.nsv", "result1686_51.nsv", "result1686_52.nsv", "result1686_53.nsv", "result1686_54.nsv", "result1686_55.nsv", "result1686_56.nsv", "result1686_57.nsv"];
val thyn = "vfmTestDefs1686";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
