Theory vfmTest2558[no_sig_docs]
Ancestors vfmTestDefs2558
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2558";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
