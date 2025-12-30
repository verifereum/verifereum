Theory vfmTest2084[no_sig_docs]
Ancestors vfmTestDefs2084
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2084";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
