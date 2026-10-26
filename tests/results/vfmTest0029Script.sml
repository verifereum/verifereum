Theory vfmTest0029[no_sig_docs]
Ancestors vfmTestDefs0029
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0029_0.nsv", "result0029_1.nsv"];
val thyn = "vfmTestDefs0029";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
