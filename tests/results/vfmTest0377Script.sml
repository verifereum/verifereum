Theory vfmTest0377[no_sig_docs]
Ancestors vfmTestDefs0377
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0377_0.nsv", "result0377_1.nsv", "result0377_2.nsv", "result0377_3.nsv", "result0377_4.nsv", "result0377_5.nsv", "result0377_6.nsv", "result0377_7.nsv", "result0377_8.nsv", "result0377_9.nsv", "result0377_10.nsv", "result0377_11.nsv", "result0377_12.nsv", "result0377_13.nsv", "result0377_14.nsv", "result0377_15.nsv", "result0377_16.nsv", "result0377_17.nsv", "result0377_18.nsv", "result0377_19.nsv", "result0377_20.nsv", "result0377_21.nsv", "result0377_22.nsv", "result0377_23.nsv"];
val thyn = "vfmTestDefs0377";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
