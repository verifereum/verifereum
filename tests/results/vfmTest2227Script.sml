Theory vfmTest2227[no_sig_docs]
Ancestors vfmTestDefs2227
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2227";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
