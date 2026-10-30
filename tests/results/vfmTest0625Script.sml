Theory vfmTest0625[no_sig_docs]
Ancestors vfmTestDefs0625
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0625_0.nsv", "result0625_1.nsv", "result0625_2.nsv"];
val thyn = "vfmTestDefs0625";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
