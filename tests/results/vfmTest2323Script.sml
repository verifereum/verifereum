Theory vfmTest2323[no_sig_docs]
Ancestors vfmTestDefs2323
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2323";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
