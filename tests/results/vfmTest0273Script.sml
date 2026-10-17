Theory vfmTest0273[no_sig_docs]
Ancestors vfmTestDefs0273
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0273_0.nsv", "result0273_1.nsv", "result0273_2.nsv", "result0273_3.nsv", "result0273_4.nsv", "result0273_5.nsv", "result0273_6.nsv", "result0273_7.nsv", "result0273_8.nsv", "result0273_9.nsv", "result0273_10.nsv", "result0273_11.nsv", "result0273_12.nsv", "result0273_13.nsv", "result0273_14.nsv", "result0273_15.nsv", "result0273_16.nsv", "result0273_17.nsv", "result0273_18.nsv", "result0273_19.nsv", "result0273_20.nsv", "result0273_21.nsv", "result0273_22.nsv", "result0273_23.nsv", "result0273_24.nsv", "result0273_25.nsv", "result0273_26.nsv", "result0273_27.nsv", "result0273_28.nsv", "result0273_29.nsv", "result0273_30.nsv", "result0273_31.nsv", "result0273_32.nsv", "result0273_33.nsv", "result0273_34.nsv", "result0273_35.nsv", "result0273_36.nsv", "result0273_37.nsv", "result0273_38.nsv", "result0273_39.nsv", "result0273_40.nsv", "result0273_41.nsv", "result0273_42.nsv", "result0273_43.nsv", "result0273_44.nsv", "result0273_45.nsv", "result0273_46.nsv", "result0273_47.nsv", "result0273_48.nsv", "result0273_49.nsv", "result0273_50.nsv", "result0273_51.nsv", "result0273_52.nsv", "result0273_53.nsv", "result0273_54.nsv", "result0273_55.nsv"];
val thyn = "vfmTestDefs0273";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
