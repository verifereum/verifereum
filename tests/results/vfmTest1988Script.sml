Theory vfmTest1988[no_sig_docs]
Ancestors vfmTestDefs1988
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1988";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
