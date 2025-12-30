Theory vfmTest0012[no_sig_docs]
Ancestors vfmTestDefs0012
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0012";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
