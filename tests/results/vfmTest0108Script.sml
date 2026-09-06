Theory vfmTest0108[no_sig_docs]
Ancestors vfmTestDefs0108
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0108_0.nsv", "result0108_1.nsv", "result0108_2.nsv", "result0108_3.nsv", "result0108_4.nsv", "result0108_5.nsv", "result0108_6.nsv", "result0108_7.nsv", "result0108_8.nsv", "result0108_9.nsv", "result0108_10.nsv", "result0108_11.nsv", "result0108_12.nsv", "result0108_13.nsv", "result0108_14.nsv", "result0108_15.nsv", "result0108_16.nsv", "result0108_17.nsv", "result0108_18.nsv", "result0108_19.nsv", "result0108_20.nsv", "result0108_21.nsv", "result0108_22.nsv", "result0108_23.nsv"];
val thyn = "vfmTestDefs0108";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
