Theory vfmTest0671[no_sig_docs]
Ancestors vfmTestDefs0671
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0671_0.nsv"];
val thyn = "vfmTestDefs0671";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
