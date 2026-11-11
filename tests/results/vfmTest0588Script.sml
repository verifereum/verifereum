Theory vfmTest0588[no_sig_docs]
Ancestors vfmTestDefs0588
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0588_0.nsv", "result0588_1.nsv", "result0588_2.nsv", "result0588_3.nsv", "result0588_4.nsv", "result0588_5.nsv", "result0588_6.nsv", "result0588_7.nsv", "result0588_8.nsv", "result0588_9.nsv", "result0588_10.nsv", "result0588_11.nsv", "result0588_12.nsv", "result0588_13.nsv", "result0588_14.nsv", "result0588_15.nsv", "result0588_16.nsv", "result0588_17.nsv", "result0588_18.nsv", "result0588_19.nsv", "result0588_20.nsv", "result0588_21.nsv", "result0588_22.nsv", "result0588_23.nsv"];
val thyn = "vfmTestDefs0588";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
