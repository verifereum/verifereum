Theory vfmTest0108[no_sig_docs]
Ancestors vfmTestDefs0108
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0108";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
