Theory vfmTest0739[no_sig_docs]
Ancestors vfmTestDefs0739
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0739";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
