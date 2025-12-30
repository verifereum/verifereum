Theory vfmTest0944[no_sig_docs]
Ancestors vfmTestDefs0944
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0944";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
