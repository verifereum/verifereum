Theory vfmTest2582[no_sig_docs]
Ancestors vfmTestDefs2582
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2582";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
