Theory vfmTest0748[no_sig_docs]
Ancestors vfmTestDefs0748
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0748_0.nsv", "result0748_1.nsv", "result0748_2.nsv", "result0748_3.nsv", "result0748_4.nsv", "result0748_5.nsv", "result0748_6.nsv", "result0748_7.nsv", "result0748_8.nsv", "result0748_9.nsv", "result0748_10.nsv", "result0748_11.nsv", "result0748_12.nsv", "result0748_13.nsv", "result0748_14.nsv", "result0748_15.nsv", "result0748_16.nsv", "result0748_17.nsv", "result0748_18.nsv", "result0748_19.nsv", "result0748_20.nsv", "result0748_21.nsv", "result0748_22.nsv", "result0748_23.nsv", "result0748_24.nsv", "result0748_25.nsv", "result0748_26.nsv", "result0748_27.nsv", "result0748_28.nsv", "result0748_29.nsv", "result0748_30.nsv", "result0748_31.nsv", "result0748_32.nsv", "result0748_33.nsv", "result0748_34.nsv", "result0748_35.nsv", "result0748_36.nsv", "result0748_37.nsv", "result0748_38.nsv", "result0748_39.nsv", "result0748_40.nsv", "result0748_41.nsv", "result0748_42.nsv", "result0748_43.nsv", "result0748_44.nsv", "result0748_45.nsv", "result0748_46.nsv", "result0748_47.nsv"];
val thyn = "vfmTestDefs0748";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
