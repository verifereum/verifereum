Theory vfmTest2007[no_sig_docs]
Ancestors vfmTestDefs2007
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2007";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
