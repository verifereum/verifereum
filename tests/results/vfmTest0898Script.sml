Theory vfmTest0898[no_sig_docs]
Ancestors vfmTestDefs0898
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0898_0.nsv"];
val thyn = "vfmTestDefs0898";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
