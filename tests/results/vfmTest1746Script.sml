Theory vfmTest1746[no_sig_docs]
Ancestors vfmTestDefs1746
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs [];
val thyn = "vfmTestDefs1746";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
