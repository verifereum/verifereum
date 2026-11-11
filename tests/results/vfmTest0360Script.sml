Theory vfmTest0360[no_sig_docs]
Ancestors vfmTestDefs0360
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0360_0.nsv", "result0360_1.nsv", "result0360_2.nsv", "result0360_3.nsv", "result0360_4.nsv", "result0360_5.nsv", "result0360_6.nsv", "result0360_7.nsv", "result0360_8.nsv", "result0360_9.nsv", "result0360_10.nsv", "result0360_11.nsv", "result0360_12.nsv", "result0360_13.nsv", "result0360_14.nsv", "result0360_15.nsv", "result0360_16.nsv", "result0360_17.nsv", "result0360_18.nsv", "result0360_19.nsv", "result0360_20.nsv", "result0360_21.nsv", "result0360_22.nsv", "result0360_23.nsv", "result0360_24.nsv", "result0360_25.nsv", "result0360_26.nsv", "result0360_27.nsv", "result0360_28.nsv", "result0360_29.nsv", "result0360_30.nsv", "result0360_31.nsv", "result0360_32.nsv", "result0360_33.nsv", "result0360_34.nsv", "result0360_35.nsv", "result0360_36.nsv", "result0360_37.nsv", "result0360_38.nsv", "result0360_39.nsv", "result0360_40.nsv", "result0360_41.nsv", "result0360_42.nsv", "result0360_43.nsv", "result0360_44.nsv", "result0360_45.nsv", "result0360_46.nsv", "result0360_47.nsv", "result0360_48.nsv", "result0360_49.nsv", "result0360_50.nsv", "result0360_51.nsv", "result0360_52.nsv", "result0360_53.nsv", "result0360_54.nsv", "result0360_55.nsv", "result0360_56.nsv", "result0360_57.nsv", "result0360_58.nsv", "result0360_59.nsv", "result0360_60.nsv", "result0360_61.nsv"];
val thyn = "vfmTestDefs0360";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
