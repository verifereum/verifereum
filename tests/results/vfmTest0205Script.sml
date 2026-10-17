Theory vfmTest0205[no_sig_docs]
Ancestors vfmTestDefs0205
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0205_0.nsv", "result0205_1.nsv", "result0205_2.nsv", "result0205_3.nsv", "result0205_4.nsv", "result0205_5.nsv"];
val thyn = "vfmTestDefs0205";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
