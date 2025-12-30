Theory vfmTest2180[no_sig_docs]
Ancestors vfmTestDefs2180
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2180";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
