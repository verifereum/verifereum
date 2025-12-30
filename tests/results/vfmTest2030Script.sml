Theory vfmTest2030[no_sig_docs]
Ancestors vfmTestDefs2030
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2030";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
