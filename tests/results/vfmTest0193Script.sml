Theory vfmTest0193[no_sig_docs]
Ancestors vfmTestDefs0193
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0193_0.nsv", "result0193_1.nsv", "result0193_2.nsv", "result0193_3.nsv", "result0193_4.nsv", "result0193_5.nsv", "result0193_6.nsv", "result0193_7.nsv", "result0193_8.nsv", "result0193_9.nsv", "result0193_10.nsv", "result0193_11.nsv", "result0193_12.nsv", "result0193_13.nsv", "result0193_14.nsv", "result0193_15.nsv", "result0193_16.nsv", "result0193_17.nsv", "result0193_18.nsv", "result0193_19.nsv", "result0193_20.nsv", "result0193_21.nsv", "result0193_22.nsv", "result0193_23.nsv", "result0193_24.nsv", "result0193_25.nsv", "result0193_26.nsv", "result0193_27.nsv", "result0193_28.nsv", "result0193_29.nsv", "result0193_30.nsv", "result0193_31.nsv", "result0193_32.nsv", "result0193_33.nsv", "result0193_34.nsv", "result0193_35.nsv", "result0193_36.nsv", "result0193_37.nsv", "result0193_38.nsv", "result0193_39.nsv", "result0193_40.nsv", "result0193_41.nsv", "result0193_42.nsv", "result0193_43.nsv", "result0193_44.nsv", "result0193_45.nsv", "result0193_46.nsv", "result0193_47.nsv", "result0193_48.nsv", "result0193_49.nsv", "result0193_50.nsv", "result0193_51.nsv", "result0193_52.nsv", "result0193_53.nsv"];
val thyn = "vfmTestDefs0193";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
