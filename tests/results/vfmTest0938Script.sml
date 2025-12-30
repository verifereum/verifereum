Theory vfmTest0938[no_sig_docs]
Ancestors vfmTestDefs0938
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0938";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
