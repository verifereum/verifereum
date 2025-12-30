Theory vfmTest0397[no_sig_docs]
Ancestors vfmTestDefs0397
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0397";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
