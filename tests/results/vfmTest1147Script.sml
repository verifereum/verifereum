Theory vfmTest1147[no_sig_docs]
Ancestors vfmTestDefs1147
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1147";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
