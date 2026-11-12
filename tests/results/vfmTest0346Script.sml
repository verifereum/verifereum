Theory vfmTest0346[no_sig_docs]
Ancestors vfmTestDefs0346
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0346_0.nsv", "result0346_1.nsv", "result0346_2.nsv", "result0346_3.nsv", "result0346_4.nsv", "result0346_5.nsv"];
val thyn = "vfmTestDefs0346";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
