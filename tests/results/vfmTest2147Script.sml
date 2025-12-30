Theory vfmTest2147[no_sig_docs]
Ancestors vfmTestDefs2147
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2147";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
