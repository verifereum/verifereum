Theory vfmTest0392[no_sig_docs]
Ancestors vfmTestDefs0392
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0392";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
