Theory vfmTest2266[no_sig_docs]
Ancestors vfmTestDefs2266
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2266";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
