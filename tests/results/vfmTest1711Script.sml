Theory vfmTest1711[no_sig_docs]
Ancestors vfmTestDefs1711
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1711";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
