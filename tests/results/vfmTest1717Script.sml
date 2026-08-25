Theory vfmTest1717[no_sig_docs]
Ancestors vfmTestDefs1717
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1717_0.nsv"];
val thyn = "vfmTestDefs1717";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
