Theory vfmTest0736[no_sig_docs]
Ancestors vfmTestDefs0736
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0736";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
