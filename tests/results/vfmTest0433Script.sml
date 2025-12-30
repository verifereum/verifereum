Theory vfmTest0433[no_sig_docs]
Ancestors vfmTestDefs0433
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0433";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
