Theory vfmTest0062[no_sig_docs]
Ancestors vfmTestDefs0062
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0062";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
