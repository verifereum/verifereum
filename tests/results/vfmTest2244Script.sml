Theory vfmTest2244[no_sig_docs]
Ancestors vfmTestDefs2244
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2244";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
