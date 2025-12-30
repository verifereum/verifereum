Theory vfmTest2366[no_sig_docs]
Ancestors vfmTestDefs2366
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2366";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
