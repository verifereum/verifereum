Theory vfmTest0882[no_sig_docs]
Ancestors vfmTestDefs0882
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0882_0.nsv", "result0882_1.nsv", "result0882_2.nsv", "result0882_3.nsv", "result0882_4.nsv", "result0882_5.nsv", "result0882_6.nsv", "result0882_7.nsv", "result0882_8.nsv", "result0882_9.nsv", "result0882_10.nsv", "result0882_11.nsv", "result0882_12.nsv", "result0882_13.nsv", "result0882_14.nsv", "result0882_15.nsv", "result0882_16.nsv", "result0882_17.nsv", "result0882_18.nsv", "result0882_19.nsv", "result0882_20.nsv", "result0882_21.nsv", "result0882_22.nsv", "result0882_23.nsv", "result0882_24.nsv", "result0882_25.nsv", "result0882_26.nsv", "result0882_27.nsv", "result0882_28.nsv", "result0882_29.nsv", "result0882_30.nsv", "result0882_31.nsv", "result0882_32.nsv", "result0882_33.nsv", "result0882_34.nsv", "result0882_35.nsv", "result0882_36.nsv", "result0882_37.nsv", "result0882_38.nsv", "result0882_39.nsv", "result0882_40.nsv", "result0882_41.nsv", "result0882_42.nsv", "result0882_43.nsv", "result0882_44.nsv", "result0882_45.nsv"];
val thyn = "vfmTestDefs0882";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
