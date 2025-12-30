Theory vfmTest0184[no_sig_docs]
Ancestors vfmTestDefs0184
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0184";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
