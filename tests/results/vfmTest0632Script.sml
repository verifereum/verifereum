Theory vfmTest0632[no_sig_docs]
Ancestors vfmTestDefs0632
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0632_0.nsv", "result0632_1.nsv", "result0632_2.nsv", "result0632_3.nsv", "result0632_4.nsv", "result0632_5.nsv", "result0632_6.nsv", "result0632_7.nsv", "result0632_8.nsv", "result0632_9.nsv"];
val thyn = "vfmTestDefs0632";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
