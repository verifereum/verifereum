Theory vfmTest0262[no_sig_docs]
Ancestors vfmTestDefs0262
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0262_0.nsv", "result0262_1.nsv", "result0262_2.nsv", "result0262_3.nsv", "result0262_4.nsv", "result0262_5.nsv", "result0262_6.nsv", "result0262_7.nsv", "result0262_8.nsv", "result0262_9.nsv", "result0262_10.nsv", "result0262_11.nsv", "result0262_12.nsv", "result0262_13.nsv", "result0262_14.nsv", "result0262_15.nsv", "result0262_16.nsv", "result0262_17.nsv", "result0262_18.nsv", "result0262_19.nsv", "result0262_20.nsv", "result0262_21.nsv", "result0262_22.nsv", "result0262_23.nsv", "result0262_24.nsv", "result0262_25.nsv", "result0262_26.nsv", "result0262_27.nsv", "result0262_28.nsv", "result0262_29.nsv", "result0262_30.nsv", "result0262_31.nsv", "result0262_32.nsv", "result0262_33.nsv", "result0262_34.nsv", "result0262_35.nsv", "result0262_36.nsv", "result0262_37.nsv", "result0262_38.nsv", "result0262_39.nsv", "result0262_40.nsv", "result0262_41.nsv", "result0262_42.nsv", "result0262_43.nsv", "result0262_44.nsv", "result0262_45.nsv", "result0262_46.nsv", "result0262_47.nsv", "result0262_48.nsv", "result0262_49.nsv", "result0262_50.nsv", "result0262_51.nsv", "result0262_52.nsv", "result0262_53.nsv", "result0262_54.nsv", "result0262_55.nsv"];
val thyn = "vfmTestDefs0262";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
