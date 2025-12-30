Theory vfmTest2522[no_sig_docs]
Ancestors vfmTestDefs2522
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2522";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
