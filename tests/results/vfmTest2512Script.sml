Theory vfmTest2512[no_sig_docs]
Ancestors vfmTestDefs2512
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2512";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
