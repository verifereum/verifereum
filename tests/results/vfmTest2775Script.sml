Theory vfmTest2775[no_sig_docs]
Ancestors vfmTestDefs2775
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2775";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
