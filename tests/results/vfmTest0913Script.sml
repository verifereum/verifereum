Theory vfmTest0913[no_sig_docs]
Ancestors vfmTestDefs0913
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0913";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
