Theory vfmTest0617[no_sig_docs]
Ancestors vfmTestDefs0617
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0617_0.nsv", "result0617_1.nsv", "result0617_2.nsv", "result0617_3.nsv", "result0617_4.nsv", "result0617_5.nsv", "result0617_6.nsv", "result0617_7.nsv", "result0617_8.nsv", "result0617_9.nsv", "result0617_10.nsv", "result0617_11.nsv", "result0617_12.nsv", "result0617_13.nsv", "result0617_14.nsv", "result0617_15.nsv", "result0617_16.nsv", "result0617_17.nsv", "result0617_18.nsv", "result0617_19.nsv", "result0617_20.nsv", "result0617_21.nsv", "result0617_22.nsv", "result0617_23.nsv", "result0617_24.nsv", "result0617_25.nsv", "result0617_26.nsv", "result0617_27.nsv", "result0617_28.nsv", "result0617_29.nsv", "result0617_30.nsv", "result0617_31.nsv", "result0617_32.nsv", "result0617_33.nsv", "result0617_34.nsv", "result0617_35.nsv", "result0617_36.nsv", "result0617_37.nsv", "result0617_38.nsv", "result0617_39.nsv", "result0617_40.nsv", "result0617_41.nsv", "result0617_42.nsv", "result0617_43.nsv", "result0617_44.nsv", "result0617_45.nsv", "result0617_46.nsv", "result0617_47.nsv", "result0617_48.nsv", "result0617_49.nsv", "result0617_50.nsv", "result0617_51.nsv", "result0617_52.nsv", "result0617_53.nsv", "result0617_54.nsv"];
val thyn = "vfmTestDefs0617";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
