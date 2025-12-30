Theory vfmTest0648[no_sig_docs]
Ancestors vfmTestDefs0648
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0648";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
