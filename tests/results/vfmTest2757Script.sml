Theory vfmTest2757[no_sig_docs]
Ancestors vfmTestDefs2757
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2757";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
