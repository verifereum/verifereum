Theory vfmTest0583[no_sig_docs]
Ancestors vfmTestDefs0583
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0583";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
