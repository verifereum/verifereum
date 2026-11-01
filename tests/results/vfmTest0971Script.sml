Theory vfmTest0971[no_sig_docs]
Ancestors vfmTestDefs0971
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0971_0.nsv", "result0971_1.nsv", "result0971_2.nsv", "result0971_3.nsv", "result0971_4.nsv", "result0971_5.nsv", "result0971_6.nsv", "result0971_7.nsv", "result0971_8.nsv", "result0971_9.nsv", "result0971_10.nsv", "result0971_11.nsv", "result0971_12.nsv", "result0971_13.nsv", "result0971_14.nsv", "result0971_15.nsv", "result0971_16.nsv", "result0971_17.nsv", "result0971_18.nsv", "result0971_19.nsv", "result0971_20.nsv", "result0971_21.nsv", "result0971_22.nsv", "result0971_23.nsv", "result0971_24.nsv", "result0971_25.nsv", "result0971_26.nsv", "result0971_27.nsv", "result0971_28.nsv", "result0971_29.nsv", "result0971_30.nsv", "result0971_31.nsv", "result0971_32.nsv", "result0971_33.nsv", "result0971_34.nsv", "result0971_35.nsv", "result0971_36.nsv", "result0971_37.nsv", "result0971_38.nsv", "result0971_39.nsv", "result0971_40.nsv", "result0971_41.nsv", "result0971_42.nsv", "result0971_43.nsv"];
val thyn = "vfmTestDefs0971";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
