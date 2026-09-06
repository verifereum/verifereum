Theory vfmTest0002[no_sig_docs]
Ancestors vfmTestDefs0002
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0002_0.nsv", "result0002_1.nsv"];
val thyn = "vfmTestDefs0002";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
