Theory vfmTest0825[no_sig_docs]
Ancestors vfmTestDefs0825
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0825";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
