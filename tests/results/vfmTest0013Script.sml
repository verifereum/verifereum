Theory vfmTest0013[no_sig_docs]
Ancestors vfmTestDefs0013
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0013_0.nsv", "result0013_1.nsv", "result0013_2.nsv", "result0013_3.nsv", "result0013_4.nsv", "result0013_5.nsv", "result0013_6.nsv", "result0013_7.nsv", "result0013_8.nsv", "result0013_9.nsv", "result0013_10.nsv", "result0013_11.nsv", "result0013_12.nsv", "result0013_13.nsv", "result0013_14.nsv", "result0013_15.nsv", "result0013_16.nsv", "result0013_17.nsv", "result0013_18.nsv", "result0013_19.nsv", "result0013_20.nsv", "result0013_21.nsv", "result0013_22.nsv", "result0013_23.nsv", "result0013_24.nsv", "result0013_25.nsv", "result0013_26.nsv", "result0013_27.nsv", "result0013_28.nsv", "result0013_29.nsv", "result0013_30.nsv", "result0013_31.nsv", "result0013_32.nsv", "result0013_33.nsv", "result0013_34.nsv", "result0013_35.nsv", "result0013_36.nsv", "result0013_37.nsv", "result0013_38.nsv", "result0013_39.nsv", "result0013_40.nsv", "result0013_41.nsv", "result0013_42.nsv", "result0013_43.nsv", "result0013_44.nsv", "result0013_45.nsv"];
val thyn = "vfmTestDefs0013";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
