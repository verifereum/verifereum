Theory vfmTest0100[no_sig_docs]
Ancestors vfmTestDefs0100
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0100_0.nsv", "result0100_1.nsv", "result0100_2.nsv", "result0100_3.nsv", "result0100_4.nsv", "result0100_5.nsv", "result0100_6.nsv", "result0100_7.nsv", "result0100_8.nsv", "result0100_9.nsv", "result0100_10.nsv", "result0100_11.nsv", "result0100_12.nsv", "result0100_13.nsv", "result0100_14.nsv", "result0100_15.nsv", "result0100_16.nsv", "result0100_17.nsv"];
val thyn = "vfmTestDefs0100";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
