Theory vfmTest0491[no_sig_docs]
Ancestors vfmTestDefs0491
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0491_0.nsv", "result0491_1.nsv", "result0491_2.nsv", "result0491_3.nsv", "result0491_4.nsv", "result0491_5.nsv", "result0491_6.nsv", "result0491_7.nsv", "result0491_8.nsv", "result0491_9.nsv", "result0491_10.nsv", "result0491_11.nsv", "result0491_12.nsv", "result0491_13.nsv", "result0491_14.nsv", "result0491_15.nsv", "result0491_16.nsv", "result0491_17.nsv", "result0491_18.nsv", "result0491_19.nsv", "result0491_20.nsv", "result0491_21.nsv", "result0491_22.nsv", "result0491_23.nsv"];
val thyn = "vfmTestDefs0491";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
