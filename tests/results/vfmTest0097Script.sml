Theory vfmTest0097[no_sig_docs]
Ancestors vfmTestDefs0097
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0097_0.nsv", "result0097_1.nsv", "result0097_2.nsv", "result0097_3.nsv", "result0097_4.nsv", "result0097_5.nsv", "result0097_6.nsv", "result0097_7.nsv", "result0097_8.nsv", "result0097_9.nsv", "result0097_10.nsv", "result0097_11.nsv", "result0097_12.nsv", "result0097_13.nsv", "result0097_14.nsv", "result0097_15.nsv", "result0097_16.nsv", "result0097_17.nsv", "result0097_18.nsv", "result0097_19.nsv", "result0097_20.nsv", "result0097_21.nsv", "result0097_22.nsv", "result0097_23.nsv", "result0097_24.nsv", "result0097_25.nsv", "result0097_26.nsv", "result0097_27.nsv", "result0097_28.nsv", "result0097_29.nsv", "result0097_30.nsv", "result0097_31.nsv", "result0097_32.nsv", "result0097_33.nsv", "result0097_34.nsv", "result0097_35.nsv", "result0097_36.nsv", "result0097_37.nsv", "result0097_38.nsv", "result0097_39.nsv", "result0097_40.nsv", "result0097_41.nsv", "result0097_42.nsv", "result0097_43.nsv", "result0097_44.nsv", "result0097_45.nsv", "result0097_46.nsv", "result0097_47.nsv", "result0097_48.nsv", "result0097_49.nsv", "result0097_50.nsv", "result0097_51.nsv", "result0097_52.nsv", "result0097_53.nsv", "result0097_54.nsv", "result0097_55.nsv"];
val thyn = "vfmTestDefs0097";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
