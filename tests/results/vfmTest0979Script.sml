Theory vfmTest0979[no_sig_docs]
Ancestors vfmTestDefs0979
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0979_0.nsv", "result0979_1.nsv"];
val thyn = "vfmTestDefs0979";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
