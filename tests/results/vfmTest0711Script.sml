Theory vfmTest0711[no_sig_docs]
Ancestors vfmTestDefs0711
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0711";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
