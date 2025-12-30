Theory vfmTest0100[no_sig_docs]
Ancestors vfmTestDefs0100
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0100";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
