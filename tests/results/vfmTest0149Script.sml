Theory vfmTest0149[no_sig_docs]
Ancestors vfmTestDefs0149
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0149_0.nsv", "result0149_1.nsv", "result0149_2.nsv", "result0149_3.nsv", "result0149_4.nsv", "result0149_5.nsv", "result0149_6.nsv", "result0149_7.nsv", "result0149_8.nsv", "result0149_9.nsv", "result0149_10.nsv", "result0149_11.nsv", "result0149_12.nsv", "result0149_13.nsv", "result0149_14.nsv", "result0149_15.nsv", "result0149_16.nsv", "result0149_17.nsv", "result0149_18.nsv", "result0149_19.nsv", "result0149_20.nsv", "result0149_21.nsv", "result0149_22.nsv", "result0149_23.nsv"];
val thyn = "vfmTestDefs0149";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
