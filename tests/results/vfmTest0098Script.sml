Theory vfmTest0098[no_sig_docs]
Ancestors vfmTestDefs0098
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0098_0.nsv", "result0098_1.nsv", "result0098_2.nsv", "result0098_3.nsv", "result0098_4.nsv", "result0098_5.nsv", "result0098_6.nsv", "result0098_7.nsv", "result0098_8.nsv", "result0098_9.nsv", "result0098_10.nsv", "result0098_11.nsv", "result0098_12.nsv", "result0098_13.nsv", "result0098_14.nsv", "result0098_15.nsv", "result0098_16.nsv", "result0098_17.nsv", "result0098_18.nsv", "result0098_19.nsv", "result0098_20.nsv", "result0098_21.nsv", "result0098_22.nsv", "result0098_23.nsv", "result0098_24.nsv", "result0098_25.nsv", "result0098_26.nsv", "result0098_27.nsv", "result0098_28.nsv", "result0098_29.nsv", "result0098_30.nsv", "result0098_31.nsv", "result0098_32.nsv", "result0098_33.nsv", "result0098_34.nsv", "result0098_35.nsv", "result0098_36.nsv", "result0098_37.nsv", "result0098_38.nsv", "result0098_39.nsv", "result0098_40.nsv", "result0098_41.nsv", "result0098_42.nsv", "result0098_43.nsv", "result0098_44.nsv", "result0098_45.nsv", "result0098_46.nsv", "result0098_47.nsv", "result0098_48.nsv", "result0098_49.nsv", "result0098_50.nsv", "result0098_51.nsv", "result0098_52.nsv", "result0098_53.nsv", "result0098_54.nsv", "result0098_55.nsv"];
val thyn = "vfmTestDefs0098";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
