Theory vfmTest2843[no_sig_docs]
Ancestors vfmTestDefs2843
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2843";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
