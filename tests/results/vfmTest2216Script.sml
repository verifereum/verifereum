Theory vfmTest2216[no_sig_docs]
Ancestors vfmTestDefs2216
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2216";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
