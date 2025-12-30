Theory vfmTest1821[no_sig_docs]
Ancestors vfmTestDefs1821
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1821";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
