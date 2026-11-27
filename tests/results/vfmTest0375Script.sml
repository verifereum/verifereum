Theory vfmTest0375[no_sig_docs]
Ancestors vfmTestDefs0375
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0375_0.nsv", "result0375_1.nsv", "result0375_2.nsv", "result0375_3.nsv", "result0375_4.nsv", "result0375_5.nsv", "result0375_6.nsv", "result0375_7.nsv", "result0375_8.nsv", "result0375_9.nsv", "result0375_10.nsv", "result0375_11.nsv", "result0375_12.nsv", "result0375_13.nsv", "result0375_14.nsv", "result0375_15.nsv", "result0375_16.nsv", "result0375_17.nsv", "result0375_18.nsv", "result0375_19.nsv", "result0375_20.nsv", "result0375_21.nsv", "result0375_22.nsv", "result0375_23.nsv", "result0375_24.nsv", "result0375_25.nsv", "result0375_26.nsv", "result0375_27.nsv", "result0375_28.nsv", "result0375_29.nsv", "result0375_30.nsv", "result0375_31.nsv", "result0375_32.nsv", "result0375_33.nsv", "result0375_34.nsv", "result0375_35.nsv", "result0375_36.nsv", "result0375_37.nsv", "result0375_38.nsv", "result0375_39.nsv", "result0375_40.nsv", "result0375_41.nsv", "result0375_42.nsv", "result0375_43.nsv", "result0375_44.nsv", "result0375_45.nsv", "result0375_46.nsv", "result0375_47.nsv", "result0375_48.nsv", "result0375_49.nsv", "result0375_50.nsv", "result0375_51.nsv", "result0375_52.nsv", "result0375_53.nsv", "result0375_54.nsv", "result0375_55.nsv", "result0375_56.nsv", "result0375_57.nsv", "result0375_58.nsv", "result0375_59.nsv", "result0375_60.nsv", "result0375_61.nsv"];
val thyn = "vfmTestDefs0375";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
