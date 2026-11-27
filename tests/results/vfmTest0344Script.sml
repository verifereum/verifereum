Theory vfmTest0344[no_sig_docs]
Ancestors vfmTestDefs0344
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0344_0.nsv", "result0344_1.nsv", "result0344_2.nsv", "result0344_3.nsv", "result0344_4.nsv", "result0344_5.nsv", "result0344_6.nsv", "result0344_7.nsv", "result0344_8.nsv", "result0344_9.nsv", "result0344_10.nsv", "result0344_11.nsv", "result0344_12.nsv", "result0344_13.nsv", "result0344_14.nsv", "result0344_15.nsv", "result0344_16.nsv", "result0344_17.nsv", "result0344_18.nsv", "result0344_19.nsv", "result0344_20.nsv", "result0344_21.nsv", "result0344_22.nsv", "result0344_23.nsv", "result0344_24.nsv", "result0344_25.nsv", "result0344_26.nsv", "result0344_27.nsv", "result0344_28.nsv", "result0344_29.nsv", "result0344_30.nsv", "result0344_31.nsv", "result0344_32.nsv", "result0344_33.nsv", "result0344_34.nsv", "result0344_35.nsv", "result0344_36.nsv", "result0344_37.nsv", "result0344_38.nsv", "result0344_39.nsv", "result0344_40.nsv", "result0344_41.nsv", "result0344_42.nsv", "result0344_43.nsv", "result0344_44.nsv", "result0344_45.nsv", "result0344_46.nsv", "result0344_47.nsv", "result0344_48.nsv", "result0344_49.nsv", "result0344_50.nsv", "result0344_51.nsv", "result0344_52.nsv", "result0344_53.nsv", "result0344_54.nsv", "result0344_55.nsv"];
val thyn = "vfmTestDefs0344";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
