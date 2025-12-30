Theory vfmTest0029[no_sig_docs]
Ancestors vfmTestDefs0029
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0029";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
