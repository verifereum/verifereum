Theory vfmTest0148[no_sig_docs]
Ancestors vfmTestDefs0148
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0148_0.nsv", "result0148_1.nsv", "result0148_2.nsv", "result0148_3.nsv", "result0148_4.nsv", "result0148_5.nsv", "result0148_6.nsv", "result0148_7.nsv", "result0148_8.nsv", "result0148_9.nsv", "result0148_10.nsv", "result0148_11.nsv", "result0148_12.nsv", "result0148_13.nsv", "result0148_14.nsv", "result0148_15.nsv", "result0148_16.nsv", "result0148_17.nsv", "result0148_18.nsv", "result0148_19.nsv", "result0148_20.nsv", "result0148_21.nsv", "result0148_22.nsv", "result0148_23.nsv", "result0148_24.nsv", "result0148_25.nsv", "result0148_26.nsv", "result0148_27.nsv", "result0148_28.nsv", "result0148_29.nsv", "result0148_30.nsv", "result0148_31.nsv", "result0148_32.nsv", "result0148_33.nsv"];
val thyn = "vfmTestDefs0148";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
