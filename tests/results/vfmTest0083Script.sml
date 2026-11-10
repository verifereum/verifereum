Theory vfmTest0083[no_sig_docs]
Ancestors vfmTestDefs0083
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0083_0.nsv", "result0083_1.nsv"];
val thyn = "vfmTestDefs0083";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
