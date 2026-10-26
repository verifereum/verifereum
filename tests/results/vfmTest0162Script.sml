Theory vfmTest0162[no_sig_docs]
Ancestors vfmTestDefs0162
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0162_0.nsv"];
val thyn = "vfmTestDefs0162";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
