Theory vfmTest0992[no_sig_docs]
Ancestors vfmTestDefs0992
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0992";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
