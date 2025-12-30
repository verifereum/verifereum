Theory vfmTest2023[no_sig_docs]
Ancestors vfmTestDefs2023
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2023";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
