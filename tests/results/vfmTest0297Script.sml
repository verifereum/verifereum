Theory vfmTest0297[no_sig_docs]
Ancestors vfmTestDefs0297
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0297_0.nsv", "result0297_1.nsv", "result0297_2.nsv", "result0297_3.nsv", "result0297_4.nsv", "result0297_5.nsv", "result0297_6.nsv", "result0297_7.nsv", "result0297_8.nsv", "result0297_9.nsv", "result0297_10.nsv", "result0297_11.nsv", "result0297_12.nsv", "result0297_13.nsv", "result0297_14.nsv", "result0297_15.nsv", "result0297_16.nsv", "result0297_17.nsv", "result0297_18.nsv", "result0297_19.nsv", "result0297_20.nsv", "result0297_21.nsv", "result0297_22.nsv", "result0297_23.nsv", "result0297_24.nsv", "result0297_25.nsv", "result0297_26.nsv", "result0297_27.nsv", "result0297_28.nsv", "result0297_29.nsv", "result0297_30.nsv", "result0297_31.nsv", "result0297_32.nsv", "result0297_33.nsv", "result0297_34.nsv", "result0297_35.nsv", "result0297_36.nsv", "result0297_37.nsv", "result0297_38.nsv", "result0297_39.nsv", "result0297_40.nsv", "result0297_41.nsv", "result0297_42.nsv", "result0297_43.nsv", "result0297_44.nsv", "result0297_45.nsv", "result0297_46.nsv", "result0297_47.nsv", "result0297_48.nsv", "result0297_49.nsv", "result0297_50.nsv", "result0297_51.nsv"];
val thyn = "vfmTestDefs0297";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
