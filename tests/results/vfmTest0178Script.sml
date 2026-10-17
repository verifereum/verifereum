Theory vfmTest0178[no_sig_docs]
Ancestors vfmTestDefs0178
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0178_0.nsv", "result0178_1.nsv", "result0178_2.nsv", "result0178_3.nsv", "result0178_4.nsv", "result0178_5.nsv", "result0178_6.nsv", "result0178_7.nsv", "result0178_8.nsv", "result0178_9.nsv", "result0178_10.nsv", "result0178_11.nsv", "result0178_12.nsv", "result0178_13.nsv", "result0178_14.nsv", "result0178_15.nsv", "result0178_16.nsv", "result0178_17.nsv", "result0178_18.nsv", "result0178_19.nsv", "result0178_20.nsv", "result0178_21.nsv", "result0178_22.nsv", "result0178_23.nsv", "result0178_24.nsv", "result0178_25.nsv", "result0178_26.nsv", "result0178_27.nsv", "result0178_28.nsv", "result0178_29.nsv", "result0178_30.nsv", "result0178_31.nsv", "result0178_32.nsv", "result0178_33.nsv", "result0178_34.nsv", "result0178_35.nsv", "result0178_36.nsv", "result0178_37.nsv", "result0178_38.nsv", "result0178_39.nsv", "result0178_40.nsv", "result0178_41.nsv", "result0178_42.nsv", "result0178_43.nsv", "result0178_44.nsv", "result0178_45.nsv", "result0178_46.nsv", "result0178_47.nsv"];
val thyn = "vfmTestDefs0178";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
