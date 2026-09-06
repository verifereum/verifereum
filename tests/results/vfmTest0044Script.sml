Theory vfmTest0044[no_sig_docs]
Ancestors vfmTestDefs0044
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0044_0.nsv", "result0044_1.nsv", "result0044_2.nsv", "result0044_3.nsv", "result0044_4.nsv", "result0044_5.nsv", "result0044_6.nsv", "result0044_7.nsv", "result0044_8.nsv", "result0044_9.nsv", "result0044_10.nsv", "result0044_11.nsv", "result0044_12.nsv", "result0044_13.nsv", "result0044_14.nsv", "result0044_15.nsv", "result0044_16.nsv", "result0044_17.nsv", "result0044_18.nsv", "result0044_19.nsv", "result0044_20.nsv", "result0044_21.nsv", "result0044_22.nsv", "result0044_23.nsv"];
val thyn = "vfmTestDefs0044";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
