Theory vfmTest1844[no_sig_docs]
Ancestors vfmTestDefs1844
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs [];
val thyn = "vfmTestDefs1844";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
