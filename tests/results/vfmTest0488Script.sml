Theory vfmTest0488[no_sig_docs]
Ancestors vfmTestDefs0488
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0488";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
