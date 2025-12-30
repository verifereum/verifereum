Theory vfmTest0851[no_sig_docs]
Ancestors vfmTestDefs0851
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0851";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
