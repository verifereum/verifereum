Theory vfmTest2703[no_sig_docs]
Ancestors vfmTestDefs2703
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2703";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
