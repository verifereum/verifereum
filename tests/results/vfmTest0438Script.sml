Theory vfmTest0438[no_sig_docs]
Ancestors vfmTestDefs0438
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0438_0.nsv", "result0438_1.nsv", "result0438_2.nsv", "result0438_3.nsv", "result0438_4.nsv", "result0438_5.nsv", "result0438_6.nsv", "result0438_7.nsv", "result0438_8.nsv", "result0438_9.nsv", "result0438_10.nsv", "result0438_11.nsv"];
val thyn = "vfmTestDefs0438";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
