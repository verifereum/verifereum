Theory vfmTest0850[no_sig_docs]
Ancestors vfmTestDefs0850
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0850_0.nsv", "result0850_1.nsv", "result0850_2.nsv", "result0850_3.nsv", "result0850_4.nsv", "result0850_5.nsv", "result0850_6.nsv", "result0850_7.nsv", "result0850_8.nsv", "result0850_9.nsv", "result0850_10.nsv", "result0850_11.nsv", "result0850_12.nsv", "result0850_13.nsv", "result0850_14.nsv", "result0850_15.nsv", "result0850_16.nsv", "result0850_17.nsv", "result0850_18.nsv", "result0850_19.nsv", "result0850_20.nsv", "result0850_21.nsv", "result0850_22.nsv", "result0850_23.nsv", "result0850_24.nsv", "result0850_25.nsv", "result0850_26.nsv", "result0850_27.nsv", "result0850_28.nsv", "result0850_29.nsv", "result0850_30.nsv", "result0850_31.nsv", "result0850_32.nsv", "result0850_33.nsv", "result0850_34.nsv", "result0850_35.nsv", "result0850_36.nsv", "result0850_37.nsv", "result0850_38.nsv", "result0850_39.nsv", "result0850_40.nsv", "result0850_41.nsv", "result0850_42.nsv", "result0850_43.nsv", "result0850_44.nsv", "result0850_45.nsv", "result0850_46.nsv", "result0850_47.nsv", "result0850_48.nsv", "result0850_49.nsv", "result0850_50.nsv", "result0850_51.nsv", "result0850_52.nsv", "result0850_53.nsv", "result0850_54.nsv", "result0850_55.nsv", "result0850_56.nsv", "result0850_57.nsv"];
val thyn = "vfmTestDefs0850";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
