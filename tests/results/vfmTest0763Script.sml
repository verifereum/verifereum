Theory vfmTest0763[no_sig_docs]
Ancestors vfmTestDefs0763
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0763";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
