Theory vfmTest1008[no_sig_docs]
Ancestors vfmTestDefs1008
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1008_0.nsv", "result1008_1.nsv", "result1008_2.nsv", "result1008_3.nsv", "result1008_4.nsv", "result1008_5.nsv", "result1008_6.nsv", "result1008_7.nsv", "result1008_8.nsv", "result1008_9.nsv", "result1008_10.nsv", "result1008_11.nsv", "result1008_12.nsv", "result1008_13.nsv", "result1008_14.nsv", "result1008_15.nsv", "result1008_16.nsv", "result1008_17.nsv", "result1008_18.nsv", "result1008_19.nsv", "result1008_20.nsv", "result1008_21.nsv", "result1008_22.nsv", "result1008_23.nsv", "result1008_24.nsv", "result1008_25.nsv", "result1008_26.nsv", "result1008_27.nsv", "result1008_28.nsv", "result1008_29.nsv", "result1008_30.nsv", "result1008_31.nsv", "result1008_32.nsv", "result1008_33.nsv", "result1008_34.nsv", "result1008_35.nsv", "result1008_36.nsv", "result1008_37.nsv", "result1008_38.nsv", "result1008_39.nsv", "result1008_40.nsv", "result1008_41.nsv", "result1008_42.nsv", "result1008_43.nsv", "result1008_44.nsv", "result1008_45.nsv", "result1008_46.nsv", "result1008_47.nsv"];
val thyn = "vfmTestDefs1008";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
