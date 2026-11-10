Theory vfmTest0207[no_sig_docs]
Ancestors vfmTestDefs0207
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0207_0.nsv"];
val thyn = "vfmTestDefs0207";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
