Theory vfmTest0866[no_sig_docs]
Ancestors vfmTestDefs0866
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0866";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
