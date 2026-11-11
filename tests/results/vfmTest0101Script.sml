Theory vfmTest0101[no_sig_docs]
Ancestors vfmTestDefs0101
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0101_0.nsv", "result0101_1.nsv", "result0101_2.nsv", "result0101_3.nsv", "result0101_4.nsv", "result0101_5.nsv", "result0101_6.nsv", "result0101_7.nsv", "result0101_8.nsv", "result0101_9.nsv", "result0101_10.nsv", "result0101_11.nsv", "result0101_12.nsv", "result0101_13.nsv", "result0101_14.nsv", "result0101_15.nsv", "result0101_16.nsv", "result0101_17.nsv"];
val thyn = "vfmTestDefs0101";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
