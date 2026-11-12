Theory vfmTest0358[no_sig_docs]
Ancestors vfmTestDefs0358
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0358_0.nsv", "result0358_1.nsv", "result0358_2.nsv", "result0358_3.nsv", "result0358_4.nsv", "result0358_5.nsv", "result0358_6.nsv", "result0358_7.nsv", "result0358_8.nsv", "result0358_9.nsv", "result0358_10.nsv", "result0358_11.nsv", "result0358_12.nsv", "result0358_13.nsv", "result0358_14.nsv", "result0358_15.nsv", "result0358_16.nsv"];
val thyn = "vfmTestDefs0358";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
